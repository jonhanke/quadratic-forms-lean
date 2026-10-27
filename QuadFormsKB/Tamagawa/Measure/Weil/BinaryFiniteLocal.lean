import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinConst
import QuadFormsKB.Tamagawa.BinaryCMDiscr

/-!
# The binary torus at a finite place: the maximal order, the principal unit windows, the local measures

**Layer:** $F$ a number field, $K/F$ quadratic with a basis $b = (1,\delta)$ of $K$ over $F$ (`hb₀ : b 0 = 1`,
`hb₁ : b 1 * b 1 = algebraMap F K d`), $d\in\mathcal O_F$ (for the torus of $\langle1,D\rangle$: $d=-D$, $\delta=\theta$,
and $E_v$ below is the algebra `QuadK D Fv` of `BinaryTorusLocal.lean`), $v$ a finite place of $F$, $F_v$, $\mathfrak o_v$,
$E_v = F_v[\omega]/(\omega^2-d)$ = `QuadraticAlgebra Fv (algebraMap F Fv d) 0`, and $\varphi_w$ = `quadLocalHom` = `qlh`
$: E_v\to K_w$, $x+y\omega\mapsto\varphi_w(x)+\delta\varphi_w(y)$, for the places $w\mid v$ of $K$ (`PlaceSet v`).

**Proves** (the finite-place facts L1–L3)
* **L1 (`isMaxInt_iff_forall`, `isMaxInt_iff_forall_places`).** The maximal order $\mathcal O_{E,v}=\{z\in E_v:\operatorname{tr}z,\,Nz\in\mathfrak o_v\}$
  (`maxOrder`, a subring; the predicate is `IsMaxInt`) is exactly the set of $z$ with $\varphi_w(z)$ integral (valuation $\le1$)
  at every $w\mid v$. *Proof:* a component is a root of $X^2-\varphi_w(\operatorname{tr}z)X+\varphi_w(Nz)$; conversely global
  integers have integral trace and norm (`isMaxInt_coordsOf`), are dense in $\prod_{w\mid v}\mathcal O_w$ (`intPlace_subset_closure`),
  and integrality of trace and norm is a closed condition. **Units** (`isMaxInt_and_norm_eq_one_iff`): $z\in\mathcal O_{E,v}$ with
  $Nz\in\mathfrak o_v^\times$ iff every component $\varphi_w(z)$ is a unit of $\mathcal O_w$.
* **L2 (`coordOrder_le_maxOrder`, `relIndex_unitWindow`).** $R_v=\mathfrak o_v[\omega]=\{x+y\omega: x,y\in\mathfrak o_v\}$ (`coordOrder`) is a subring of
  $\mathcal O_{E,v}$. For $v(\varpi)=q^{-1}$, $k\ge1$ and $\varpi^k\mathcal O_{E,v}\subseteq R_v$, the map $1+\varpi^ky\mapsto y\bmod R_v$ is a group
  isomorphism from $1+\varpi^k\mathcal O_{E,v}$ modulo $1+\varpi^kR_v$ onto $\mathcal O_{E,v}/R_v$ (`unitWindow`), so
  $[1+\varpi^k\mathcal O_{E,v}:1+\varpi^kR_v]=[\mathcal O_{E,v}:R_v]$. (For the CM data, $[\mathcal O_{E,v}:R_v]=N(v)^{c_v}$, in `BinaryFiniteLocalCM.lean`.)
* **L3 (`window_iff`, `prod_omegaV_window_ratio`).** For $k\ge1$ the set of $z$ all of whose components lie in $1+\varpi^k\mathcal O_w$ is
  $1+\varpi^k\mathcal O_{E,v}$, and
  $$\prod_{w\mid v}\frac{\omega_w(1+\varpi^k\mathcal O_w)}{\omega_w(\mathcal O_w^\times)}=N(v)^{-2k}\,(1-N(v)^{-1})^{-1}\,(1-\chi_{K/F}(v)N(v)^{-1})^{-1},$$
  $\omega_w$ = `omegaV w`, $\mathcal O_w^\times$ = `unitsVSub w`, $\chi_{K/F}$ = `Binary.Rel.relChar` ($1$ split, $-1$ inert, $0$ ramified).
  *Proof:* per place the ratio is $N(w)^{-e_wk}(1-N(w)^{-1})^{-1}$ (`omegaV_window_ratio`), then
  $\prod_wN(w)^{e_w}=N(v)^2$ (`prod_q_pow_ramE`) and the fibre product over the primes of $K$ above $v$ (`prod_places_inv_one_sub`,
  via the bijection `placeSetEquiv` between the places over $v$ and `Ideal.primesOver`).
* `exists_integer_near`: strong approximation of coordinates in $F_v^2$ with integral components by global integers.

Sources: Cassels–Fröhlich, *Algebraic Number Theory*, Ch. II (Cassels), §10, (10.2), p. 57, and §12, Lemma, p. 61 [unverified locators];
Weil, *Adeles and Algebraic Groups*, §2.3, p. 21, §3.7, pp. 64–65 [unverified pages]; Neukirch, *Algebraic Number Theory*, Ch. II, §8 [unverified].
-/

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero Matrix QuadFormsKB.Lattices
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Tamagawa LocalDensity

section GlobalTraceNorm

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))

include hb₀ hb₁ in
/-- The matrix of multiplication by $\delta=b_1$ in the basis $(1,\delta)$ is $\begin{pmatrix}0&d\\1&0\end{pmatrix}$. -/
theorem leftMulMatrix_delta :
    Algebra.leftMulMatrix bK (bK 1) = !![0, (d : F); 1, 0] := by
  generalize (d : F) = c at hb₁ ⊢
  have h : bK 1 * bK 1 = c • bK 0 := by rw [hb₁, hb₀, Algebra.algebraMap_eq_smul_one]
  have h0 : bK 1 * bK 0 = bK 1 := by rw [hb₀, mul_one]
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases i <;> fin_cases j <;> simp [h0, h]

include hb₀ hb₁ in
/-- The matrix of multiplication by $a+b\delta$ in the basis $(1,\delta)$ is $\begin{pmatrix}a&db\\b&a\end{pmatrix}$. -/
theorem leftMulMatrix_coords (a b : F) :
    Algebra.leftMulMatrix bK (algebraMap F K a + algebraMap F K b * bK 1) =
      !![a, (d : F) * b; b, a] := by
  rw [map_add, map_mul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
    map_one, leftMulMatrix_delta hb₀ hb₁]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

include hb₀ hb₁ in
/-- The matrix of multiplication by $x\in K$ in the basis $(1,\delta)$, in terms of the coordinates $x_0,x_1$ of $x$. -/
theorem leftMulMatrix_eq (x : K) :
    Algebra.leftMulMatrix bK x = !![bK.repr x 0, (d : F) * bK.repr x 1; bK.repr x 1, bK.repr x 0] := by
  have hx : algebraMap F K (bK.repr x 0) + algebraMap F K (bK.repr x 1) * bK 1 = x := by
    conv_rhs => rw [← bK.sum_repr x]
    rw [Fin.sum_univ_two, hb₀, Algebra.smul_def, Algebra.smul_def, mul_one]
  have := leftMulMatrix_coords hb₀ hb₁ (bK.repr x 0) (bK.repr x 1)
  rwa [hx] at this

include hb₀ hb₁ in
/-- $\operatorname{Tr}_{K/F}(x_0 + x_1\delta) = 2x_0$. -/
theorem trace_eq_repr (x : K) : Algebra.trace F K x = 2 * bK.repr x 0 := by
  rw [Algebra.trace_eq_matrix_trace bK, leftMulMatrix_eq hb₀ hb₁, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring

include hb₀ hb₁ in
/-- $N_{K/F}(x_0 + x_1\delta) = x_0^2 - d\,x_1^2$. -/
theorem norm_eq_repr (x : K) :
    Algebra.norm F x = bK.repr x 0 * bK.repr x 0 - (d : F) * bK.repr x 1 * bK.repr x 1 := by
  rw [Algebra.norm_eq_matrix_det bK, leftMulMatrix_eq hb₀ hb₁, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]

end GlobalTraceNorm

/-! ### The maximal order at a finite place: integrality of trace and norm -/

section Local

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Ev" => QuadraticAlgebra (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (d : F)) 0

variable (d) in
/-- **Integrality of trace and norm in $E_v = F_v[\omega]/(\omega^2 - d)$:** $\operatorname{tr}z\in\mathfrak o_v$ and
$Nz\in\mathfrak o_v$ (valuations at most $1$). The maximal order $\mathcal O_{E,v}$ is the set of such $z$. -/
def IsMaxInt (z : Ev) : Prop :=
  Valued.v (QuadraticAlgebra.trace z) ≤ 1 ∧ Valued.v (QuadraticAlgebra.norm z) ≤ 1

/-- The trace of $x+y\omega\in E_v$ (with $\omega^2=d$, no linear term) is $2x$. -/
theorem trace_eq_two_mul (z : Ev) : QuadraticAlgebra.trace z = 2 * z.re := by
  rw [QuadraticAlgebra.trace_def, zero_mul, add_zero]

/-- The norm of $x+y\omega\in E_v$ is $x^2-dy^2$. -/
theorem norm_eq_sq_sub (z : Ev) :
    QuadraticAlgebra.norm z = z.re * z.re - algebraMap F Fv (d : F) * z.im * z.im := by
  rw [QuadraticAlgebra.norm_def, zero_mul, zero_mul, add_zero]

/-- `IsMaxInt` in coordinates: $v(2x)\le1$ and $v(x^2-dy^2)\le1$. -/
theorem isMaxInt_mk_iff (x y : Fv) :
    IsMaxInt d v (⟨x, y⟩ : Ev) ↔
      Valued.v (2 * x) ≤ 1 ∧ Valued.v (x * x - algebraMap F Fv (d : F) * y * y) ≤ 1 := by
  rw [IsMaxInt, trace_eq_two_mul, norm_eq_sq_sub]

include hb₁ in
/-- **Integral trace and norm give integral components.** If $\operatorname{tr}z, Nz\in\mathfrak o_v$ then
$\varphi_w(z)$ is integral for every $w\mid v$: it is a root of $X^2 - \varphi_w(\operatorname{tr}z)X + \varphi_w(Nz)$. -/
theorem valued_qlh_le_one_of_isMaxInt {z : Ev} (hz : IsMaxInt d v z) (w : PlaceSet (K := K) v) :
    Valued.v (qlh hb₁ v w z) ≤ 1 := by
  have hsq := congrArg (qlh hb₁ v w) (QuadraticAlgebra.sq_eq_trace_smul_sub_norm z)
  simp only [map_pow, map_sub, Algebra.smul_def, map_mul] at hsq
  rw [qlh_algebraMap hb₁ w, qlh_algebraMap hb₁ w] at hsq
  have ht := localRingHom_valued_le_one v w.1 w.2 _ hz.1
  have hn := localRingHom_valued_le_one v w.1 w.2 _ hz.2
  by_contra hu
  push Not at hu
  set u := qlh hb₁ v w z
  have h1 : Valued.v (u ^ 2) ≤ Valued.v u := by
    rw [hsq]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]
      calc _ ≤ 1 * Valued.v u := mul_le_mul' ht le_rfl
        _ = _ := one_mul _
    · exact hn.trans hu.le
  rw [map_pow] at h1
  have hu0 : (0 : ℤᵐ⁰) < Valued.v u := lt_trans zero_lt_one hu
  have : Valued.v u * 1 < Valued.v u * Valued.v u := mul_lt_mul_of_pos_left hu hu0
  rw [mul_one, ← sq] at this
  exact absurd h1 (not_le.2 this)

/-- An element of $F$ that is integral over $\mathbb Z$ has valuation at most $1$ at every finite place. -/
theorem valuation_le_one_of_isIntegral (y : F) (hy : IsIntegral ℤ y) : v.valuation F y ≤ 1 := by
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (R := ℤ) (B := F) (A := 𝓞 F)).mp hy
  rw [← ha]
  exact v.valuation_le_one a

variable (bK) in
/-- The coordinates in $F_v^2$ of a global integer $a\in\mathcal O_K$ with respect to the basis $(1,\delta)$. -/
def coordsOf (a : 𝓞 K) : Fin 2 → Fv := fun i => algebraMap F Fv (bK.repr (a : K) i)

/-- The coordinates of a global integer $a\in\mathcal O_K$ are sent by `localPi` to its diagonal image in
$\prod_{w\mid v}K_w$. -/
theorem localPi_coordsOf (a : 𝓞 K) : localPi bK v (coordsOf bK v a) = diagPlace v (a : K) := by
  funext w
  rw [localPi_apply]
  have h1 := congrArg (algebraMap K (w.1.adicCompletion K)) (bK.sum_repr (a : K))
  simp only [map_sum, Algebra.smul_def, map_mul] at h1
  refine Eq.trans ?_ h1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hφ : localRingHom v w.1 w.2 (algebraMap F Fv (bK.repr (a : K) i)) =
      algebraMap K (w.1.adicCompletion K) (algebraMap F K (bK.repr (a : K) i)) :=
    localRingHom_algebraMap v w.1 w.2 _
  show _ * localRingHom v w.1 w.2 (algebraMap F Fv (bK.repr (a : K) i)) = _
  rw [hφ]
  exact mul_comm _ _

include hb₀ hb₁ in
/-- **Global integers have integral trace and norm at every finite place:** $a\in\mathcal O_K$ gives an element of the
maximal order $\mathcal O_{E,v}$ (in the coordinates of $(1,\delta)$). -/
theorem isMaxInt_coordsOf (a : 𝓞 K) :
    IsMaxInt d v (⟨coordsOf bK v a 0, coordsOf bK v a 1⟩ : Ev) := by
  rw [isMaxInt_mk_iff]
  have hint : IsIntegral ℤ (a : K) := a.isIntegral_coe
  constructor
  · have h1 := valuation_le_one_of_isIntegral v _ (Algebra.isIntegral_trace (R := ℤ) hint)
    rw [trace_eq_repr hb₀ hb₁] at h1
    have : (2 : Fv) * coordsOf bK v a 0 = algebraMap F Fv (2 * bK.repr (a : K) 0) := by simp only [coordsOf, map_mul, map_ofNat]
    rw [this, valued_algebraMap]
    exact h1
  · have h1 := valuation_le_one_of_isIntegral v _ (Algebra.isIntegral_norm (R := ℤ) F hint)
    rw [norm_eq_repr hb₀ hb₁] at h1
    have : coordsOf bK v a 0 * coordsOf bK v a 0 - algebraMap F Fv (d : F) * coordsOf bK v a 1 * coordsOf bK v a 1 =
        algebraMap F Fv (bK.repr (a : K) 0 * bK.repr (a : K) 0 - (d : F) * bK.repr (a : K) 1 * bK.repr (a : K) 1) := by
      simp [coordsOf]
    rw [this, valued_algebraMap]
    exact h1

include hb₀ hb₁ in
/-- **L1, converse direction.** If $\varphi_w(z)$ is integral at every $w\mid v$, then $\operatorname{tr}z$ and $Nz$ are
integral. *Proof:* the integers $\mathcal O_K$ are dense in $\prod_{w\mid v}\mathcal O_w$ (`intPlace_subset_closure`), the
set of coordinates with integral trace and norm is closed, and global integers lie in it (`isMaxInt_coordsOf`). -/
theorem isMaxInt_of_forall {z : Ev} (hz : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) ≤ 1) :
    IsMaxInt d v z := by
  set C : Set (Fin 2 → Fv) := {c | IsMaxInt d v (⟨c 0, c 1⟩ : Ev)} with hC
  have hCc : IsClosed C := by
    have hcl : IsClosed {y : Fv | Valued.v y ≤ 1} := Valued.isClosed_valuationSubring Fv
    have e : C = (fun c : Fin 2 → Fv => 2 * c 0) ⁻¹' {y | Valued.v y ≤ 1} ∩
        (fun c : Fin 2 → Fv => c 0 * c 0 - algebraMap F Fv (d : F) * c 1 * c 1) ⁻¹' {y | Valued.v y ≤ 1} := by
      ext c; simp only [hC, mem_ofPred_eq, isMaxInt_mk_iff, mem_inter_iff, mem_preimage]
    rw [e]
    refine (hcl.preimage ?_).inter (hcl.preimage ?_)
    · fun_prop
    · fun_prop
  set c : Fin 2 → Fv := ![z.re, z.im] with hc
  have hmem : localPi bK v c ∈ intPlace (K := K) v := by
    intro w
    have := hz w
    rw [localPi_apply, Fin.sum_univ_two, hb₀]
    simp only [hc, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ((1 : K) : w.1.adicCompletion K) = algebraMap K (w.1.adicCompletion K) 1 from rfl, map_one, one_mul]
    exact this
  have hcl := intPlace_subset_closure (K := K) v hmem
  have h1 : localPiCLE bK v '' C ⊇ Set.range (fun a : 𝓞 K => diagPlace v (a : K)) := by
    rintro _ ⟨a, rfl⟩
    refine ⟨coordsOf bK v a, ?_, ?_⟩
    · exact isMaxInt_coordsOf hb₀ hb₁ v a
    · rw [localPiCLE_apply, localPi_coordsOf]
  have h2 : IsClosed (localPiCLE bK v '' C) := (localPiCLE bK v).toHomeomorph.isClosedMap _ hCc
  have h3 := closure_minimal h1 h2 hcl
  obtain ⟨c', hc'C, hc'⟩ := h3
  have : c' = c := (localPiCLE bK v).injective hc'
  rw [this] at hc'C
  exact hc'C

include hb₀ hb₁ in
/-- **L1: the maximal order at $v$ is cut out by the places over $v$.** For $z\in E_v = F_v[\omega]/(\omega^2-d)$:
$\operatorname{tr}z$ and $Nz$ are integral at $v$ if and only if $\varphi_w(z)\in K_w$ is integral for every place
$w\mid v$ of $K$ (valuation $\le1$), where $\varphi_w$ = `qlh` = `quadLocalHom`, $x+y\omega\mapsto\varphi_w(x)+\delta\varphi_w(y)$.
*Proof:* ($\Rightarrow$) $\varphi_w(z)$ is a root of the monic polynomial $X^2-\varphi_w(\operatorname{tr}z)X+\varphi_w(Nz)$
with integral coefficients (`valued_qlh_le_one_of_isMaxInt`); ($\Leftarrow$) density of $\mathcal O_K$ in
$\prod_{w\mid v}\mathcal O_w$ and closedness of the integrality conditions (`isMaxInt_of_forall`). -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §12, Lemma, (12.1), p. 61, and §10, (10.2), p. 57 [unverified]"]
theorem isMaxInt_iff_forall (z : Ev) :
    IsMaxInt d v z ↔ ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) ≤ 1 :=
  ⟨fun hz w => valued_qlh_le_one_of_isMaxInt hb₁ v hz w, isMaxInt_of_forall hb₀ hb₁ v⟩

include hb₀ hb₁ in
/-- **L1, in the form of the statement:** $\operatorname{tr}z,\,Nz\in\mathfrak o_v$ iff `quadLocalHom hb₁ v w h z` has
valuation $\le1$ for every place $w\mid v$ of $K$. -/
theorem isMaxInt_iff_forall_places (z : Ev) :
    IsMaxInt d v z ↔
      ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v), Valued.v (quadLocalHom hb₁ v w h z) ≤ 1 :=
  ⟨fun hz w h => (isMaxInt_iff_forall hb₀ hb₁ v z).1 hz ⟨w, h⟩, fun hz =>
    (isMaxInt_iff_forall hb₀ hb₁ v z).2 fun w => hz w.1 w.2⟩

include hb₀ hb₁ in
/-- **The maximal order $\mathcal O_{E,v}$ of $E_v = F_v[\omega]/(\omega^2-d)$** as a subring:
$\{z : \operatorname{tr}z\in\mathfrak o_v,\ Nz\in\mathfrak o_v\}$ (a subring by L1: it is the preimage of
$\prod_{w\mid v}\mathcal O_w$). -/
def maxOrder : Subring Ev where
  carrier := {z | IsMaxInt d v z}
  mul_mem' := fun {z z'} hz hz' => by
    rw [mem_ofPred_eq, isMaxInt_iff_forall hb₀ hb₁] at hz hz' ⊢
    intro w
    rw [map_mul, map_mul]
    exact mul_le_one' (hz w) (hz' w)
  one_mem' := by
    rw [mem_ofPred_eq, isMaxInt_iff_forall hb₀ hb₁]
    intro w; rw [map_one, map_one]
  add_mem' := fun {z z'} hz hz' => by
    rw [mem_ofPred_eq, isMaxInt_iff_forall hb₀ hb₁] at hz hz' ⊢
    intro w
    rw [map_add]
    exact (Valuation.map_add _ _ _).trans (max_le (hz w) (hz' w))
  zero_mem' := by
    rw [mem_ofPred_eq, isMaxInt_iff_forall hb₀ hb₁]
    intro w; rw [map_zero, map_zero]; exact zero_le
  neg_mem' := fun {z} hz => by
    rw [mem_ofPred_eq, isMaxInt_iff_forall hb₀ hb₁] at hz ⊢
    intro w
    rw [map_neg, Valuation.map_neg]
    exact hz w

include hb₀ hb₁ in
theorem mem_maxOrder_iff (z : Ev) : z ∈ maxOrder hb₀ hb₁ v ↔ IsMaxInt d v z := Iff.rfl

include hb₀ hb₁ in
/-- Membership in $\mathcal O_{E,v}$ in terms of the places over $v$. -/
theorem mem_maxOrder_iff_forall (z : Ev) :
    z ∈ maxOrder hb₀ hb₁ v ↔ ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) ≤ 1 :=
  isMaxInt_iff_forall hb₀ hb₁ v z

theorem isMaxInt_star {z : Ev} (hz : IsMaxInt d v z) : IsMaxInt d v (star z) := by
  unfold IsMaxInt at hz ⊢
  rwa [QuadraticAlgebra.trace_star, QuadraticAlgebra.norm_star]

theorem eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : ℤᵐ⁰) = a * b := h.symm
    _ ≤ a * 1 := mul_le_mul' le_rfl hb
    _ = a := mul_one a

include hb₀ hb₁ in
/-- If every component of $z$ is a unit, $z$ has an inverse in the maximal order. -/
theorem exists_inv_of_forall_eq_one {z : Ev} (h : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) = 1) :
    ∃ y : Ev, z * y = 1 ∧ IsMaxInt d v y := by
  obtain ⟨y, hy⟩ := exists_quadLocalHom_eq hb₀ hb₁ v (fun w => (qlh hb₁ v w z)⁻¹)
  have hy' : ∀ w : PlaceSet (K := K) v, qlh hb₁ v w y = (qlh hb₁ v w z)⁻¹ := hy
  have hyv : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w y) = 1 := fun w => by
    rw [hy', map_inv₀, h w, inv_one]
  refine ⟨y, ?_, (isMaxInt_iff_forall hb₀ hb₁ v y).2 fun w => (hyv w).le⟩
  refine quadLocalHom_injective hb₀ hb₁ v (fun w => ?_)
  show qlh hb₁ v w (z * y) = qlh hb₁ v w 1
  rw [map_mul, map_one, hy', mul_inv_cancel₀]
  intro h0
  have := h w
  rw [h0, map_zero] at this
  exact zero_ne_one this

include hb₀ hb₁ in
/-- **L1, units.** For $z\in E_v$: $z\in\mathcal O_{E,v}$ and $Nz\in\mathfrak o_v^\times$ (that is, $z\in\mathcal O_{E,v}^\times$)
if and only if every component $\varphi_w(z)$, $w\mid v$, is a unit of $\mathcal O_w$ (valuation exactly $1$).
*Proof:* ($\Rightarrow$) $\varphi_w(z)\varphi_w(\bar z)=\varphi_w(Nz)$ with both factors integral; ($\Leftarrow$) the
inverse of $z$ has components $\varphi_w(z)^{-1}$, hence lies in $\mathcal O_{E,v}$, so $Nz\cdot N(z^{-1}) = 1$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §12, Lemma, (12.1), p. 61, and §10, (10.2), p. 57 [unverified]"]
theorem isMaxInt_and_norm_eq_one_iff {z : Ev} :
    (IsMaxInt d v z ∧ Valued.v (QuadraticAlgebra.norm z) = 1) ↔
      ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) = 1 := by
  constructor
  · rintro ⟨hz, hN⟩ w
    have h1 := valued_qlh_le_one_of_isMaxInt hb₁ v hz w
    have h2 := valued_qlh_le_one_of_isMaxInt hb₁ v (isMaxInt_star v hz) w
    have e := congrArg (qlh hb₁ v w) (QuadraticAlgebra.algebraMap_norm_eq_mul_star z)
    rw [qlh_algebraMap hb₁ w, map_mul] at e
    have h3 : Valued.v (qlh hb₁ v w z) * Valued.v (qlh hb₁ v w (star z)) = 1 := by
      rw [← map_mul, ← e]
      exact (valued_localRingHom_eq_one_iff w.1 w.2 _).2 hN
    exact eq_one_of_mul_eq_one_of_le_one h1 h2 h3
  · intro h
    have hz : IsMaxInt d v z := (isMaxInt_iff_forall hb₀ hb₁ v z).2 fun w => (h w).le
    refine ⟨hz, ?_⟩
    obtain ⟨y, hzy, hyO⟩ := exists_inv_of_forall_eq_one hb₀ hb₁ v h
    have hn : Valued.v (QuadraticAlgebra.norm z) * Valued.v (QuadraticAlgebra.norm y) = 1 := by
      rw [← map_mul, ← map_mul, hzy, map_one, map_one]
    exact eq_one_of_mul_eq_one_of_le_one hz.2 hyO.2 hn

variable (d) in
/-- **The order $R_v = \mathfrak o_v[\omega]$**: both coordinates of $x + y\omega$ lie in $\mathfrak o_v$. -/
def coordOrder : Subring Ev where
  carrier := {z | CL v 0 z}
  mul_mem' := fun {z z'} hz hz' => by simpa using CL.mul hz hz'
  one_mem' := CL_one
  add_mem' := fun {z z'} hz hz' => CL.add hz hz'
  zero_mem' := CL.zero 0
  neg_mem' := fun {z} hz => CL.neg hz

theorem mem_coordOrder_iff (z : Ev) : z ∈ coordOrder d v ↔ Valued.v z.re ≤ 1 ∧ Valued.v z.im ≤ 1 := by
  show CL v 0 z ↔ _
  simp [CL]

include hb₀ hb₁ in
/-- **L2, inclusion:** $R_v = \mathfrak o_v[\omega]\subseteq\mathcal O_{E,v}$. -/
theorem coordOrder_le_maxOrder : coordOrder d v ≤ maxOrder hb₀ hb₁ v := by
  intro z hz
  rw [mem_maxOrder_iff_forall hb₀ hb₁]
  intro w
  have := pl_of_cl hb₀ hb₁ (v := v) hz w
  simpa using this

include hb₀ hb₁ in
theorem algebraMap_mem_maxOrder {c : Fv} (hc : Valued.v c ≤ 1) : algebraMap Fv Ev c ∈ maxOrder hb₀ hb₁ v := by
  refine coordOrder_le_maxOrder hb₀ hb₁ v ?_
  exact CL.algebraMap (k := 0) (by simpa using hc)

/-! ### The principal unit windows $1+\varpi^kS$ and their indices (L2) -/

variable (d) in
/-- $\varpi^kS = \{\varpi^ky : y\in S\}\subseteq E_v$ for a subring $S$. -/
def scalSet (ϖ : Fv) (k : ℕ) (S : Subring Ev) : Set Ev :=
  {x | ∃ y ∈ S, x = algebraMap Fv Ev (ϖ ^ k) * y}

variable (d) in
/-- **The principal unit group $1+\varpi^kS$** of a subring $S\subseteq E_v$, as a subgroup of $E_v^\times$: the units
$u$ with $u,u^{-1}\in S$ and $u-1\in\varpi^kS$. (Requiring $u^{-1}\in S$ makes the set closed under inverses
without completeness; for $S=\mathcal O_{E,v}$ and $k\ge1$ it is exactly $\{1+\varpi^ky : y\in S\}$, see
`exists_mem_unitWindow`.) -/
def unitWindow (ϖ : Fv) (k : ℕ) (S : Subring Ev) : Subgroup Evˣ where
  carrier := {u | (u : Ev) ∈ S ∧ ((u⁻¹ : Evˣ) : Ev) ∈ S ∧ ((u : Ev) - 1) ∈ scalSet d v ϖ k S}
  mul_mem' := by
    rintro u u' ⟨hu, hu', y, hy, hyu⟩ ⟨hw, hw', y', hy', hyw⟩
    refine ⟨?_, ?_, y * (u' : Ev) + y', ?_, ?_⟩
    · rw [Units.val_mul]; exact S.mul_mem hu hw
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact S.mul_mem hw' hu'
    · exact S.add_mem (S.mul_mem hy hw) hy'
    · rw [Units.val_mul]; linear_combination (u' : Ev) * hyu + hyw
  one_mem' := ⟨S.one_mem, by simp, 0, S.zero_mem, by simp⟩
  inv_mem' := by
    rintro u ⟨hu, hu', y, hy, hyu⟩
    refine ⟨hu', by simpa using hu, -(y * ((u⁻¹ : Evˣ) : Ev)), S.neg_mem (S.mul_mem hy hu'), ?_⟩
    have hm : (u : Ev) * ((u⁻¹ : Evˣ) : Ev) = 1 := Units.mul_inv u
    linear_combination (-((u⁻¹ : Evˣ) : Ev)) * hyu + hm

variable (d) in
/-- $y_u = \varpi^{-k}(u-1)$, the coordinate of $u\in1+\varpi^kS$. -/
def yOf (ϖ : Fv) (k : ℕ) (u : Evˣ) : Ev := algebraMap Fv Ev ((ϖ ^ k)⁻¹) * ((u : Ev) - 1)

theorem yOf_spec {ϖ : Fv} (hϖ0 : ϖ ≠ 0) (k : ℕ) (u : Evˣ) :
    (u : Ev) - 1 = algebraMap Fv Ev (ϖ ^ k) * yOf d v ϖ k u := by
  unfold yOf
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), map_one, one_mul]

theorem yOf_mem {ϖ : Fv} (hϖ0 : ϖ ≠ 0) {k : ℕ} {S : Subring Ev} {u : Evˣ} (hu : u ∈ unitWindow d v ϖ k S) :
    yOf d v ϖ k u ∈ S := by
  obtain ⟨-, -, y, hy, hyu⟩ := hu
  have : yOf d v ϖ k u = y := by
    unfold yOf
    rw [hyu, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), map_one, one_mul]
  rw [this]; exact hy

theorem yOf_mul {ϖ : Fv} (hϖ0 : ϖ ≠ 0) (k : ℕ) (u u' : Evˣ) :
    yOf d v ϖ k (u * u') = yOf d v ϖ k u + yOf d v ϖ k u' + algebraMap Fv Ev (ϖ ^ k) * (yOf d v ϖ k u * yOf d v ϖ k u') := by
  have hAB : algebraMap Fv Ev (ϖ ^ k) * algebraMap Fv Ev ((ϖ ^ k)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), map_one]
  unfold yOf
  rw [Units.val_mul]
  linear_combination (-(algebraMap Fv Ev ((ϖ ^ k)⁻¹) * ((u : Ev) - 1) * ((u' : Ev) - 1))) * hAB

include hb₀ hb₁ in
/-- If $u, u^{-1}\in\mathcal O_{E,v}$ and $u\in R_v$, then $u^{-1}\in R_v$ ($u^{-1} = (Nu)^{-1}\bar u$ with
$Nu\in\mathfrak o_v^\times$). -/
theorem inv_mem_coordOrder {u : Evˣ} (huO : (u : Ev) ∈ maxOrder hb₀ hb₁ v)
    (hu'O : ((u⁻¹ : Evˣ) : Ev) ∈ maxOrder hb₀ hb₁ v) (huR : (u : Ev) ∈ coordOrder d v) :
    ((u⁻¹ : Evˣ) : Ev) ∈ coordOrder d v := by
  have hn : Valued.v (QuadraticAlgebra.norm (u : Ev)) * Valued.v (QuadraticAlgebra.norm ((u⁻¹ : Evˣ) : Ev)) = 1 := by
    rw [← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one]
  have hN1 : Valued.v (QuadraticAlgebra.norm (u : Ev)) = 1 :=
    eq_one_of_mul_eq_one_of_le_one huO.2 hu'O.2 hn
  have hN0 : QuadraticAlgebra.norm (u : Ev) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hN1; exact zero_ne_one hN1
  have hAN : algebraMap Fv Ev (QuadraticAlgebra.norm (u : Ev))⁻¹ * algebraMap Fv Ev (QuadraticAlgebra.norm (u : Ev)) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hN0, map_one]
  have e := QuadraticAlgebra.algebraMap_norm_eq_mul_star (u : Ev)
  have hm : (u : Ev) * ((u⁻¹ : Evˣ) : Ev) = 1 := Units.mul_inv u
  have hid : ((u⁻¹ : Evˣ) : Ev) = algebraMap Fv Ev (QuadraticAlgebra.norm (u : Ev))⁻¹ * star (u : Ev) := by
    linear_combination (-(((u⁻¹ : Evˣ) : Ev))) * hAN +
      (((u⁻¹ : Evˣ) : Ev) * algebraMap Fv Ev (QuadraticAlgebra.norm (u : Ev))⁻¹) * e +
      (algebraMap Fv Ev (QuadraticAlgebra.norm (u : Ev))⁻¹ * star (u : Ev)) * hm
  rw [hid]
  refine (coordOrder d v).mul_mem ?_ (CL.star huR)
  exact CL.algebraMap (k := 0) (by rw [map_inv₀, hN1, inv_one]; simp)

include hb₀ hb₁ in
/-- **Principal units are units of $\mathcal O_{E,v}$.** For $k\ge1$ and $y\in\mathcal O_{E,v}$, the element $1+\varpi^ky$
is a unit of $E_v$ whose inverse lies in $\mathcal O_{E,v}$, i.e. it lies in `unitWindow` of the maximal order. -/
theorem exists_mem_unitWindow {ϖ : Fv} (hϖ : Valued.v ϖ = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k) {y : Ev}
    (hy : y ∈ maxOrder hb₀ hb₁ v) :
    ∃ u ∈ unitWindow d v ϖ k (maxOrder hb₀ hb₁ v), (u : Ev) = 1 + algebraMap Fv Ev (ϖ ^ k) * y := by
  set u0 : Ev := 1 + algebraMap Fv Ev (ϖ ^ k) * y with hu0
  have hϖ1 : Valued.v (ϖ ^ k) ≤ 1 := by
    rw [map_pow, hϖ, ← WithZero.exp_nsmul]
    exact (exp_le_exp.2 (by simp)).trans_eq exp_zero
  have hAO : algebraMap Fv Ev (ϖ ^ k) * y ∈ maxOrder hb₀ hb₁ v :=
    (maxOrder hb₀ hb₁ v).mul_mem (algebraMap_mem_maxOrder hb₀ hb₁ v hϖ1) hy
  have h1 : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w u0) = 1 := by
    intro w
    have hlt : Valued.v (qlh hb₁ v w (algebraMap Fv Ev (ϖ ^ k) * y)) < 1 := by
      rw [map_mul, qlh_algebraMap hb₁ w, map_mul, map_pow, map_pow, valued_localRingHom_exp v w.1 w.2 hϖ]
      have hyw := (mem_maxOrder_iff_forall hb₀ hb₁ v y).1 hy w
      have hlt0 : exp (-((ramE v w.1 : ℤ) * 1)) ^ k < 1 := by
        rw [← WithZero.exp_nsmul, ← exp_zero]
        refine exp_lt_exp.2 ?_
        have := one_le_ramE v w.1 w.2
        simp only [nsmul_eq_mul, mul_one]
        have : (1 : ℤ) ≤ ramE v w.1 := by exact_mod_cast this
        have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
        nlinarith
      calc _ ≤ exp (-((ramE v w.1 : ℤ) * 1)) ^ k * 1 := mul_le_mul' le_rfl hyw
        _ < 1 := by rwa [mul_one]
    rw [hu0, map_add, map_one, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hlt), map_one]
  obtain ⟨y', hy1, hy2⟩ := exists_inv_of_forall_eq_one hb₀ hb₁ v h1
  refine ⟨Units.mkOfMulEqOne u0 y' hy1, ⟨?_, ?_, y, hy, ?_⟩, rfl⟩
  · exact (maxOrder hb₀ hb₁ v).add_mem (maxOrder hb₀ hb₁ v).one_mem hAO
  · exact hy2
  · show u0 - 1 = _
    rw [hu0]; ring

include hb₀ hb₁ in
/-- **L2, the index of principal units** (general form). Let $\varpi\in F_v$ have $v(\varpi) = q^{-1}$ and $k\ge1$ with
$\varpi^k\mathcal O_{E,v}\subseteq R_v$. Then
$$[\,1+\varpi^k\mathcal O_{E,v} : 1+\varpi^kR_v\,] = [\,\mathcal O_{E,v} : R_v\,],$$
through the group isomorphism $1+\varpi^ky\mapsto y\bmod R_v$ onto the additive quotient $\mathcal O_{E,v}/R_v$
(a homomorphism because $(1+\varpi^ky)(1+\varpi^ky') = 1+\varpi^k(y+y'+\varpi^kyy')$ and $\varpi^k\mathcal O_{E,v}\subseteq R_v$). -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §12, Lemma, (12.1), p. 61 [unverified]"]
theorem relIndex_unitWindow {ϖ : Fv} (hϖ : Valued.v ϖ = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k)
    (hkS : ∀ y ∈ maxOrder hb₀ hb₁ v, algebraMap Fv Ev (ϖ ^ k) * y ∈ coordOrder d v) :
    (unitWindow d v ϖ k (coordOrder d v)).relIndex (unitWindow d v ϖ k (maxOrder hb₀ hb₁ v)) =
      (coordOrder d v).toAddSubgroup.relIndex (maxOrder hb₀ hb₁ v).toAddSubgroup := by
  classical
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; rw [map_zero] at hϖ; exact exp_ne_zero hϖ.symm
  have hϖ1 : Valued.v (ϖ ^ k) ≤ 1 := by
    rw [map_pow, hϖ, ← WithZero.exp_nsmul]
    exact (exp_le_exp.2 (by simp)).trans_eq exp_zero
  set O := maxOrder hb₀ hb₁ v with hO
  set R := coordOrder d v with hR
  have hAR : algebraMap Fv Ev (ϖ ^ k) ∈ R := CL.algebraMap (k := 0) (by simpa using hϖ1)
  let H : AddSubgroup O.toAddSubgroup := R.toAddSubgroup.addSubgroupOf O.toAddSubgroup
  have hyO : ∀ u : unitWindow d v ϖ k O, yOf d v ϖ k u.1 ∈ O.toAddSubgroup := fun u => yOf_mem v hϖ0 u.2
  let f : unitWindow d v ϖ k O → Multiplicative (O.toAddSubgroup ⧸ H) := fun u =>
    Multiplicative.ofAdd (QuotientAddGroup.mk ⟨yOf d v ϖ k u.1, hyO u⟩)
  have hf : ∀ u u', f (u * u') = f u * f u' := by
    intro u u'
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add, ← QuotientAddGroup.mk_add]
    congr 1
    refine QuotientAddGroup.eq.2 ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    have hmul : yOf d v ϖ k (u * u' : unitWindow d v ϖ k O).1 =
        yOf d v ϖ k u.1 + yOf d v ϖ k u'.1 + algebraMap Fv Ev (ϖ ^ k) * (yOf d v ϖ k u.1 * yOf d v ϖ k u'.1) :=
      yOf_mul v hϖ0 k u.1 u'.1
    show -(yOf d v ϖ k (u * u' : unitWindow d v ϖ k O).1) + (yOf d v ϖ k u.1 + yOf d v ϖ k u'.1) ∈ R
    rw [hmul]
    have : -(yOf d v ϖ k u.1 + yOf d v ϖ k u'.1 + algebraMap Fv Ev (ϖ ^ k) * (yOf d v ϖ k u.1 * yOf d v ϖ k u'.1)) +
        (yOf d v ϖ k u.1 + yOf d v ϖ k u'.1) =
        -(algebraMap Fv Ev (ϖ ^ k) * (yOf d v ϖ k u.1 * yOf d v ϖ k u'.1)) := by ring
    rw [this]
    exact R.neg_mem (hkS _ (O.mul_mem (hyO u) (hyO u')))
  let ψ : unitWindow d v ϖ k O →* Multiplicative (O.toAddSubgroup ⧸ H) := MonoidHom.mk' f hf
  have hψ : ∀ u, ψ u = f u := fun u => rfl
  -- kernel
  have hker : ψ.ker = (unitWindow d v ϖ k R).subgroupOf (unitWindow d v ϖ k O) := by
    ext u
    rw [MonoidHom.mem_ker, hψ, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd _ = 1 ↔ _
    rw [ofAdd_eq_one, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro hy
      have hy' : yOf d v ϖ k u.1 ∈ R := hy
      have hspec := yOf_spec (d := d) v hϖ0 k u.1
      have huR : (u.1 : Ev) ∈ R := by
        have : (u.1 : Ev) = 1 + algebraMap Fv Ev (ϖ ^ k) * yOf d v ϖ k u.1 := by rw [← hspec]; ring
        rw [this]; exact R.add_mem R.one_mem (R.mul_mem hAR hy')
      obtain ⟨huO, hu'O, -⟩ := u.2
      exact ⟨huR, inv_mem_coordOrder hb₀ hb₁ v huO hu'O huR, yOf d v ϖ k u.1, hy', hspec⟩
    · intro hu
      exact yOf_mem v hϖ0 hu
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨q', rfl⟩ := Multiplicative.ofAdd.surjective q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q'
    obtain ⟨u, hu, hue⟩ := exists_mem_unitWindow hb₀ hb₁ v hϖ hk (y := (x : Ev)) x.2
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [hψ]
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    congr 1
    apply Subtype.ext
    show yOf d v ϖ k u = (x : Ev)
    unfold yOf
    rw [hue, add_sub_cancel_left, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), map_one, one_mul]
  calc (unitWindow d v ϖ k R).relIndex (unitWindow d v ϖ k O) = ψ.ker.index := by rw [hker]; rfl
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ = Nat.card (Multiplicative (O.toAddSubgroup ⧸ H)) := by
      rw [MonoidHom.range_eq_top.2 hsurj]; exact Subgroup.card_top
    _ = Nat.card (O.toAddSubgroup ⧸ H) := Nat.card_congr Multiplicative.toAdd
    _ = _ := rfl

end Local

/-! ### The places over $v$ as the primes over $\mathfrak p_v$ -/

section PlaceEquiv

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

/-- **The places $w\mid v$ of $K$ are the primes of $\mathcal O_K$ over $\mathfrak p_v$.** -/
def placeSetEquiv : PlaceSet (K := K) v ≃ v.asIdeal.primesOver (𝓞 K) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩
  invFun P :=
    haveI := P.2.2
    ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.1⟩,
      HeightOneSpectrum.ext (P.2.2.over.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem absNorm_placeSetEquiv (w : PlaceSet (K := K) v) :
    Ideal.absNorm (placeSetEquiv v w).1 = Ideal.absNorm w.1.asIdeal := rfl

/-- **The local Euler factors over $v$:** $\prod_{w\mid v}(1-N(w)^{-1})^{-1} = (1-N(v)^{-1})^{-1}
(1-\chi_{K/F}(v)N(v)^{-1})^{-1}$, with $\chi_{K/F}(v) = 1, -1, 0$ for split, inert, ramified $v$. -/
theorem prod_places_inv_one_sub (hdeg : Module.finrank F K = 2) :
    ∏ w : PlaceSet (K := K) v, (1 - (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹)⁻¹ =
      (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ * (1 - (Binary.Rel.relChar K v : ℝ) * (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ := by
  have h := Binary.Rel.localFactor_eq (E := K) hdeg v 1
  simp only [Real.rpow_neg_one] at h
  rw [← Fintype.prod_equiv (placeSetEquiv v) (fun w : PlaceSet (K := K) v => (1 - (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹)⁻¹)
    (fun P : v.asIdeal.primesOver (𝓞 K) => (1 - (Ideal.absNorm P.1 : ℝ)⁻¹)⁻¹) (fun w => rfl)] at h
  exact h

end PlaceEquiv

/-! ### The window at one place: $\omega_w(1+\mathfrak p_w^m)/\omega_w(\mathcal O_w^\times)$ -/

section PlaceMeasure

variable {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

/-- **The ratio at one place:** for $m\ge1$,
$$\frac{\omega_w(1+\mathfrak p_w^m)}{\omega_w(\mathcal O_w^\times)} = \frac{N(w)^{-m}}{1-N(w)^{-1}}$$
($\omega_w(1+\mathfrak p_w^m) = \operatorname{vol}(\mathfrak p_w^m) = N(w)^{-m}\operatorname{vol}(\mathcal O_w)$ and
$\omega_w(\mathcal O_w^\times) = (1-N(w)^{-1})\operatorname{vol}(\mathcal O_w)$, the self-dual volumes). -/
theorem omegaV_window_ratio {m : ℕ} (hm : 1 ≤ m) :
    (omegaV w {r : (w.adicCompletion L)ˣ | Valued.v ((r : w.adicCompletion L) - 1) ≤ exp (-(m : ℤ))}).toReal /
        (omegaV w (unitsVSub w)).toReal =
      (Ideal.absNorm w.asIdeal : ℝ)⁻¹ ^ m * (1 - (Ideal.absNorm w.asIdeal : ℝ)⁻¹)⁻¹ := by
  have hq : DVR.q (w.adicCompletionIntegers L) = Ideal.absNorm w.asIdeal := NF.q_completion w
  have hV : volO w = Analysis.selfDualV w (Analysis.latticeV w 0 : Set (w.adicCompletion L)) := by
    rw [volO, coe_adicCompletionIntegers_eq]
  have hVpos : 0 < (Analysis.selfDualV w (Analysis.latticeV w 0 : Set (w.adicCompletion L))).toReal :=
    ENNReal.toReal_pos (selfDualV_latticeV_ne_zero w 0) (selfDualV_latticeV_ne_top w 0)
  have hN : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := one_lt_absNorm w
  have hN0 : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by linarith
  have h1 : (0 : ℝ) ≤ 1 - (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hN.le
  have h2 : 0 < 1 - (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hN
  rw [omegaV_oneAdd w hm, omegaV_unitsVSub, selfDualV_unitsV, selfDualV_latticeV_nat, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofReal h1, hV, hq]
  field_simp
  rw [← mul_pow, mul_one_div_cancel hN0.ne', one_pow]

end PlaceMeasure

/-! ### L3: the window at the places of $K$ -/

section Window

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Ev" => QuadraticAlgebra (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (d : F)) 0

include hb₀ hb₁ in
/-- **L3, the window as a set.** Let $\varpi\in F_v$ with $v(\varpi)=q^{-1}$ and $k\in\mathbb N$. For $z\in E_v$, every
component $\varphi_w(z)$, $w\mid v$, lies in $1+\varpi^k\mathcal O_w$ (that is,
$|\varphi_w(z)-1|_w\le|\varphi_w(\varpi)|_w^k$) if and only if $z\in1+\varpi^k\mathcal O_{E,v}$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §12, Lemma, (12.1), p. 61 [unverified]"]
theorem window_iff {ϖ : Fv} (hϖ : Valued.v ϖ = exp (-1 : ℤ)) (k : ℕ) (z : Ev) :
    (∀ w : PlaceSet (K := K) v,
        Valued.v (qlh hb₁ v w z - 1) ≤ Valued.v (localRingHom v w.1 w.2 ϖ) ^ k) ↔
      ∃ y ∈ maxOrder hb₀ hb₁ v, z = 1 + algebraMap Fv Ev (ϖ ^ k) * y := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; rw [map_zero] at hϖ; exact exp_ne_zero hϖ.symm
  have hne : ∀ w : PlaceSet (K := K) v, Valued.v (localRingHom v w.1 w.2 ϖ) ^ k ≠ 0 := fun w => by
    rw [valued_localRingHom_exp v w.1 w.2 hϖ]
    exact pow_ne_zero _ exp_ne_zero
  constructor
  · intro h
    refine ⟨algebraMap Fv Ev ((ϖ ^ k)⁻¹) * (z - 1), ?_, ?_⟩
    · rw [mem_maxOrder_iff_forall hb₀ hb₁]
      intro w
      have hb := h w
      have e : qlh hb₁ v w (z - 1) = qlh hb₁ v w z - 1 := by rw [map_sub, map_one]
      rw [map_mul, qlh_algebraMap hb₁ w, e]
      simp only [map_inv₀, map_pow, map_mul]
      calc _ ≤ (Valued.v (localRingHom v w.1 w.2 ϖ) ^ k)⁻¹ * Valued.v (localRingHom v w.1 w.2 ϖ) ^ k :=
            mul_le_mul' le_rfl hb
        _ = 1 := inv_mul_cancel₀ (hne w)
    · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), map_one, one_mul]; ring
  · rintro ⟨y, hy, rfl⟩ w
    have hyw := (mem_maxOrder_iff_forall hb₀ hb₁ v y).1 hy w
    rw [map_add, map_one, add_sub_cancel_left, map_mul, qlh_algebraMap hb₁ w, map_pow, map_mul, map_pow]
    calc _ ≤ Valued.v (localRingHom v w.1 w.2 ϖ) ^ k * 1 := mul_le_mul' le_rfl hyw
      _ = _ := mul_one _

include hb₀ hb₁ in
/-- **L3, the measure of the window.** For $k\ge1$,
$$\prod_{w\mid v}\frac{\omega_w(1+\varpi^k\mathcal O_w)}{\omega_w(\mathcal O_w^\times)} =
N(v)^{-2k}\,(1-N(v)^{-1})^{-1}\,(1-\chi_{K/F}(v)N(v)^{-1})^{-1},$$
with $\omega_w$ = `omegaV w` and $\mathcal O_w^\times$ = `unitsVSub w`. *Proof:* per place the ratio is
$N(w)^{-e_wk}(1-N(w)^{-1})^{-1}$ (`omegaV_window_ratio`, as $v_w(\varpi)=q_w^{-e_w}$); then
$\prod_wN(w)^{e_w}=N(v)^2$ (`prod_q_pow_ramE`) and $\prod_w(1-N(w)^{-1})^{-1}=(1-N(v)^{-1})^{-1}
(1-\chi N(v)^{-1})^{-1}$ (`prod_places_inv_one_sub`). -/
@[kb "weil1982" "§2.3, p. 21 and §3.7, pp. 64-65 (local ratios of ω_w) [unverified page]"]
theorem prod_omegaV_window_ratio {ϖ : Fv} (hϖ : Valued.v ϖ = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k) :
    ∏ w : PlaceSet (K := K) v,
        ((omegaV w.1 {r : (w.1.adicCompletion K)ˣ |
            Valued.v ((r : w.1.adicCompletion K) - 1) ≤ Valued.v (localRingHom v w.1 w.2 ϖ) ^ k}).toReal /
          (omegaV w.1 (unitsVSub w.1)).toReal) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ (2 * k) * (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ *
        (1 - (Binary.Rel.relChar K v : ℝ) * (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ := by
  have hdeg : Module.finrank F K = 2 := by rw [Module.finrank_eq_card_basis bK]; simp
  have hwin : ∀ w : PlaceSet (K := K) v,
      Valued.v (localRingHom v w.1 w.2 ϖ) ^ k = exp (-((ramE v w.1 * k : ℕ) : ℤ)) := fun w => by
    rw [valued_localRingHom_exp v w.1 w.2 hϖ, ← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  have h1 : ∀ w : PlaceSet (K := K) v, 1 ≤ ramE v w.1 * k := fun w =>
    Nat.mul_pos (one_le_ramE v w.1 w.2) hk
  have hq : ∀ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) = (Ideal.absNorm w.1.asIdeal : ℝ) :=
    fun w => by rw [NF.q_completion w.1]
  have hq0 : (DVR.q (v.adicCompletionIntegers F) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by rw [NF.q_completion v]
  have hprod := prod_q_pow_ramE hb₀ hb₁ v
  simp only [hq, hq0] at hprod
  have hset : ∀ w : PlaceSet (K := K) v,
      {r : (w.1.adicCompletion K)ˣ | Valued.v ((r : w.1.adicCompletion K) - 1) ≤ Valued.v (localRingHom v w.1 w.2 ϖ) ^ k} =
        {r : (w.1.adicCompletion K)ˣ | Valued.v ((r : w.1.adicCompletion K) - 1) ≤ exp (-((ramE v w.1 * k : ℕ) : ℤ))} :=
    fun w => by rw [hwin w]
  simp_rw [hset]
  rw [Finset.prod_congr rfl (fun w _ => omegaV_window_ratio w.1 (h1 w)), Finset.prod_mul_distrib,
    prod_places_inv_one_sub v hdeg, mul_assoc]
  congr 1
  · have : ∀ w : PlaceSet (K := K) v, (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ ^ (ramE v w.1 * k) =
        (((Ideal.absNorm w.1.asIdeal : ℝ) ^ ramE v w.1)⁻¹) ^ k := fun w => by
      rw [pow_mul, inv_pow]
    simp_rw [this]
    rw [Finset.prod_pow, Finset.prod_inv_distrib, hprod, pow_mul, inv_pow (Ideal.absNorm v.asIdeal : ℝ) 2]

end Window

/-! ### Approximation of integral coordinates by global integers -/

section Approx

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  (bK : Module.Basis (Fin 2) F K) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Strong approximation for the coordinates.** If $c\in F_v^2$ has integral components at all places $w\mid v$
(`localPi bK v c ∈ intPlace v`), there is a global integer $a\in\mathcal O_K$ whose coordinates in the basis $b$ are
congruent to $c$ modulo $\mathfrak o_v^2$. -/
theorem exists_integer_near {c : Fin 2 → Fv} (hc : localPi bK v c ∈ intPlace (K := K) v) :
    ∃ a : 𝓞 K, ∀ i, Valued.v (coordsOf bK v a i - c i) ≤ 1 := by
  set N : Set (Fin 2 → Fv) := {c' | ∀ i, Valued.v (c' i - c i) ≤ 1} with hN
  have hNo : IsOpen N := by
    have e : N = ⋂ i, (fun c' : Fin 2 → Fv => c' i - c i) ⁻¹' {y | Valued.v y ≤ 1} := by
      ext c'; simp [hN]
    rw [e]
    exact isOpen_iInter_of_finite fun i =>
      (Valued.isOpen_valuationSubring Fv).preimage (by fun_prop)
  have hopen : IsOpen (localPiCLE bK v '' N) := (localPiCLE bK v).toHomeomorph.isOpenMap N hNo
  have hmem : localPi bK v c ∈ localPiCLE bK v '' N :=
    ⟨c, fun i => by simp, rfl⟩
  obtain ⟨_, ⟨c', hc'N, rfl⟩, ⟨a, ha⟩⟩ := mem_closure_iff.1 (intPlace_subset_closure (K := K) v hc) _ hopen hmem
  have : c' = coordsOf bK v a := by
    apply (localPiCLE bK v).injective
    calc localPiCLE bK v c' = diagPlace v (a : K) := ha.symm
      _ = localPiCLE bK v (coordsOf bK v a) := by rw [localPiCLE_apply, localPi_coordsOf]
  exact ⟨a, this ▸ hc'N⟩

end Approx

end QuadFormsKB.Tamagawa.Measure.Weil
