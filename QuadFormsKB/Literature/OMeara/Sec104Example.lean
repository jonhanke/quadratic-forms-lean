/-
# O'Meara Example 104:6: a proper spinor genus with two proper classes in dimension 2

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^2$ with the form $Q(a, b) = 18ab + 2b^2$ (`omeara104_6Form`), all finite
spots; $L = \mathbb Z^2$ (`omeara104_6L`), and $K = \mathbb Z\,\tfrac14 x + \mathbb Z\,4y$ (`omeara104_6K`, the image of $L$
under $\operatorname{diag}(\tfrac14, 4)$), where $x = e_0$, $y = e_1$.

**Proves** Example 104:6 (O'Meara 1973, §104, pp. 319–320, `omeara104_6`): $V$ is a hyperbolic plane (regular and
isotropic, so the set of finite spots is indefinite for $V$), $K \in \operatorname{spn}^+L$, but $K \notin
\operatorname{cls}^+L$ (in fact $K \notin \operatorname{cls}L$: $L$ represents $2$ and $K$ does not). So the condition
$\dim V \ge 3$ of Theorem 104:5 cannot be dropped.

*Reconstruction.* The Gram matrices of $L$ and $K$ are lost in the scan ("$L \cong (\ ,2)$ in $x, y$", "$K \cong
(\ ,32)$ in $\tfrac14x, 4y$", with a stray "9"). O'Meara's argument needs: $L = \mathbb Zx + \mathbb Zy$ with
$Q(x) = 0$, $Q(y) = 2$ in his normalization $B(x, x) = Q(x)$, $L_2$ and $K_2$ unimodular of norm $2\mathbb Z_2$ (so
$B(x, y) = m$ is odd), $K_p = L_p$ for odd $p$, $L$ representing $2$ and $K$ not. $K$ has matrix
$\begin{pmatrix}0&m\\m&32\end{pmatrix}$ and represents $2$ if and only if $m$ divides $15$; we take $m = 9$ (matching
the stray "9"): $L \cong \begin{pmatrix}0&9\\9&2\end{pmatrix}$, $K \cong \begin{pmatrix}0&9\\9&32\end{pmatrix}$. In the
library's normalization ($B(x, y) = Q(x + y) - Q(x) - Q(y)$) this is $Q(a, b) = 18ab + 2b^2$. The local rotation at
$2$ is O'Meara's $\varphi_2 = \operatorname{diag}(\tfrac14, 4)$ in the hyperbolic base $x, w$ with $w = x - 9y$
(Example 55:1: spinor norm $\tfrac14 \in \mathbb Q_2^{\times 2}$); here it is even a rational element of $O'(V)$, the
product $\tau_{x + w}\tau_{x + w/4}$ of two symmetries.
-/
import QuadFormsKB.Literature.OMeara.Sec102

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **The form** $Q(a, b) = 18ab + 2b^2$ of Example 104:6 (O'Meara's matrix $\begin{pmatrix}0&9\\9&2\end{pmatrix}$). -/
def omeara104_6Form : QuadForm ℚ 2 := QuadForm.ofUpper ![![0, 18], ![0, 2]]

/-- $\operatorname{diag}(\tfrac14, 4) \in \mathrm{GL}_2(\mathbb Q)$. -/
def omeara104_6P : GL (Fin 2) ℚ :=
  Matrix.nonsingInvUnit (Matrix.diagonal ![1 / 4, 4]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    exact isUnit_iff_ne_zero.mpr (by norm_num))

/-- **The lattice** $L = \mathbb Z^2$ of Example 104:6. -/
def omeara104_6L : Lat ℚ 2 := ⟨intVec, intVec_isLattice⟩

/-- **The lattice** $K = \mathbb Z\,\tfrac14 x + \mathbb Z\,4y$ of Example 104:6. -/
def omeara104_6K : Lat ℚ 2 := Lat.image omeara104_6P omeara104_6L

private theorem f_evalIn {K : Type*} [CommRing K] [Algebra ℚ K] (x : Fin 2 → K) :
    omeara104_6Form.evalIn K x = 18 * (x 0 * x 1) + 2 * (x 1 * x 1) := by
  simp [omeara104_6Form, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two, map_ofNat]
  ring

private theorem f_hessian : omeara104_6Form.hessian = !![0, 18; 18, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [QuadForm.hessian, omeara104_6Form, QuadForm.ofUpper]

private theorem f_nondeg : omeara104_6Form.Nondegenerate := by
  rw [QuadForm.Nondegenerate, f_hessian, Matrix.det_fin_two_of]; norm_num

private theorem f_iso : omeara104_6Form.IsotropicIn ℚ :=
  ⟨![1, 0], fun h => by have := congrFun h 0; simp at this, by rw [f_evalIn]; simp⟩

private theorem int_of_range {y : ℚ} (h : y ∈ (algebraMap (𝓞 ℚ) ℚ).range) : ∃ m : ℤ, y = m := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
  have h1 : (((Rat.ringOfIntegersEquiv a : ℤ)) : 𝓞 ℚ) = a :=
    (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply a)
  conv_lhs => rw [← h1]
  simp

private theorem P_val : (omeara104_6P : GL (Fin 2) ℚ).val = Matrix.diagonal ![1 / 4, 4] := rfl

private theorem K_mem {z : Fin 2 → ℚ} (hz : z ∈ omeara104_6K.1) :
    ∃ a b : ℤ, z = ![(a : ℚ) / 4, 4 * b] := by
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨a, ha⟩ := int_of_range (mem_intVec.mp hy 0)
  obtain ⟨b, hb⟩ := int_of_range (mem_intVec.mp hy 1)
  refine ⟨a, b, ?_⟩
  ext i
  fin_cases i
  · simp [P_val, Matrix.mulVec, dotProduct, ← ha, ← hb, Matrix.diagonal]; ring
  · simp [P_val, Matrix.mulVec, dotProduct, ← ha, ← hb, Matrix.diagonal]

private theorem not_isometric :
    ¬ IsIsometric omeara104_6Form omeara104_6L.1 omeara104_6K.1 := by
  rintro ⟨γ, hγ, hK⟩
  have h1 : (![0, 1] : Fin 2 → ℚ) ∈ omeara104_6L.1 := by
    refine mem_intVec_iff_exists.mpr ⟨![0, 1], ?_⟩
    ext i; fin_cases i <;> simp
  have h2 : γ.val *ᵥ ![0, 1] ∈ omeara104_6K.1 := by
    rw [← hK]; exact mulVec_mem_glImage h1
  obtain ⟨a, b, hab⟩ := K_mem h2
  have hQ := evalIn_mulVec_of_mem omeara104_6Form hγ ![0, 1]
  rw [hab, f_evalIn, f_evalIn] at hQ
  simp at hQ
  have h3 : (9 * a * b + 16 * b * b : ℚ) = 1 := by linarith
  have hZ : 9 * a * b + 16 * b * b = 1 := by exact_mod_cast h3
  have h4 : b * (9 * a + 16 * b) = 1 := by linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h4 with rfl | rfl <;> omega

/-- **The rational rotation** $\varphi = \tau_{x+w}\tau_{x+w/4}$ (with $x = e_0$, $w = e_0 - 9e_1$). -/
private def phi : orthGroup omeara104_6Form ℚ :=
  symmProd omeara104_6Form ℚ [![2, -9], ![5 / 4, -9 / 4]]

private theorem hqa : omeara104_6Form.evalIn ℚ ![2, -9] = -162 := by
  rw [f_evalIn]; norm_num

private theorem hqb : omeara104_6Form.evalIn ℚ ![5 / 4, -9 / 4] = -81 / 2 := by
  rw [f_evalIn]; norm_num

private theorem phi_mem : phi ∈ spinorKernel omeara104_6Form ℚ := by
  refine ⟨[![2, -9], ![5 / 4, -9 / 4]], ⟨?_, by simp, ?_⟩, rfl⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hqa]; norm_num
    · rw [hqb]; norm_num
  · refine ⟨81, ?_⟩
    simp only [valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hqa, hqb]
    norm_num

private theorem phi_val : (phi : GL (Fin 2) ℚ).val = !![1 / 4, -5 / 12; 0, 4] := by
  have ha : omeara104_6Form.evalIn ℚ ![2, -9] ≠ 0 := by rw [hqa]; norm_num
  have hb : omeara104_6Form.evalIn ℚ ![5 / 4, -9 / 4] ≠ 0 := by rw [hqb]; norm_num
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply]
  have e : (phi : GL (Fin 2) ℚ).val *ᵥ y =
      ((symm omeara104_6Form ℚ ![2, -9] : GL (Fin 2) ℚ).val) *ᵥ
        (((symm omeara104_6Form ℚ ![5 / 4, -9 / 4] : GL (Fin 2) ℚ).val) *ᵥ y) := by
    rw [Matrix.mulVec_mulVec]
    simp [phi, symmProd]
  rw [e, symm_mulVec _ _ hb, symm_mulVec _ _ ha, hqa, hqb]
  ext i
  fin_cases i <;>
    simp [f_hessian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- $\begin{pmatrix}1&5/3\\0&1\end{pmatrix}$, the unit with $P = \varphi U$. -/
private def Uq : GL (Fin 2) ℚ :=
  ⟨!![1, 5 / 3; 0, 1], !![1, -5 / 3; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem P_eq : omeara104_6P = (phi : GL (Fin 2) ℚ) * Uq := by
  apply Units.ext
  rw [Units.val_mul, phi_val, P_val]
  show _ = !![1 / 4, -5 / 12; 0, 4] * !![1, 5 / 3; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem Pinv_val : ((omeara104_6P⁻¹ : GL (Fin 2) ℚ)).val = Matrix.diagonal ![4, 1 / 4] := by
  rw [Matrix.coe_units_inv, P_val]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

/-- $q \in F$ is integral at $\mathfrak p$ (as an element of $F_\mathfrak p$). -/
private def IntAt {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (q : F) : Prop :=
  Valued.v (algebraMap F (v.adicCompletion F) q) ≤ 1

private theorem IntAt.zero {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IntAt v (0 : F) := by
  simp [IntAt]

private theorem IntAt.neg {F : Type*} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {q : F}
    (h : IntAt v q) : IntAt v (-q) := by
  simpa [IntAt] using h

private theorem IntAt.div {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (m r : 𝓞 F) (hr : r ∉ v.asIdeal) (q : F) (hq : q = (m : F) / (r : F)) : IntAt v q := by
  subst hq
  rw [IntAt, valued_algebraMap, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hr,
    div_one]
  exact v.intValuation_le_one _

private theorem locAct_mul_unit {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} (g U : GL (Fin n) F) (hU : ∀ i j, IntAt v (U.val i j))
    (hU' : ∀ i j, IntAt v ((U⁻¹).val i j)) :
    locAct v (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (g * U)) (std v) =
      locAct v (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g) (std v) := by
  rw [map_mul, locAct_mul]
  congr 1
  ext y
  rw [mem_locAct]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mulVec_mem_std v (fun i j => hU i j) hz
  · intro hy
    refine ⟨(GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) U)⁻¹.val *ᵥ y, ?_,
      mulVec_inv_mulVec _ y⟩
    rw [← map_inv]
    exact mulVec_mem_std v (fun i j => hU' i j) hy

private theorem nmem_four {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    (4 : 𝓞 ℚ) ∉ v.asIdeal := by
  intro h4
  apply h2
  have h4' : (2 : 𝓞 ℚ) * 2 ∈ v.asIdeal := by rwa [show (2 : 𝓞 ℚ) * 2 = 4 by norm_num]
  rcases v.isPrime.mem_or_mem h4' with h | h <;> exact h

private theorem nmem_three {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    (3 : 𝓞 ℚ) ∉ v.asIdeal := by
  intro h3
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  rw [show (1 : 𝓞 ℚ) = 3 - 2 by norm_num]
  exact v.asIdeal.sub_mem h3 h2

private theorem diag_int (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℚ) (ha : IntAt v a) (hb : IntAt v b)
    (i j : Fin 2) : IntAt v (Matrix.diagonal ![a, b] i j) := by
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq]; fin_cases i; exacts [ha, hb]
  · rw [Matrix.diagonal_apply_ne _ hij]; exact IntAt.zero v

private theorem P_int (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    (∀ i j, IntAt v ((omeara104_6P : GL (Fin 2) ℚ).val i j)) ∧
      (∀ i j, IntAt v ((omeara104_6P⁻¹ : GL (Fin 2) ℚ).val i j)) := by
  have e1 : IntAt v (1 / 4 : ℚ) := IntAt.div v 1 4 (nmem_four h2) _ (by simp [map_ofNat])
  have e4 : IntAt v (4 : ℚ) := IntAt.div v 4 1 (fun h => v.isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr h)) _ (by simp [map_ofNat])
  rw [P_val, Pinv_val]
  exact ⟨diag_int v _ _ e1 e4, diag_int v _ _ e4 e1⟩

private theorem Uq_int (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    (∀ i j, IntAt v (Uq.val i j)) ∧ (∀ i j, IntAt v ((Uq⁻¹).val i j)) := by
  have h3 := nmem_three h2
  have e1 : IntAt v (1 : ℚ) := by simp [IntAt]
  have e5 : IntAt v (5 / 3 : ℚ) := IntAt.div v 5 3 h3 _ (by simp [map_ofNat])
  have e5' : IntAt v (-5 / 3 : ℚ) := IntAt.div v (-5) 3 h3 _ (by simp [map_ofNat, neg_div])
  have e0 : IntAt v (0 : ℚ) := IntAt.zero v
  constructor
  · intro i j; fin_cases i <;> fin_cases j
    exacts [e1, e5, e0, e1]
  · intro i j; fin_cases i <;> fin_cases j
    exacts [e1, e5', e0, e1]

open Classical in
/-- The adele equal to $\gamma$ at the primes in $S$ and $1$ elsewhere ($S$ cofinitely false). -/
private def kEltGen {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)
    (γ : orthGroup Q F) (S : HeightOneSpectrum (𝓞 F) → Prop)
    (hS : ∀ᶠ v in Filter.cofinite, ¬ S v) : OAf Q :=
  ⟨fun v => if S v then orthMap Q (v.adicCompletion F) γ else 1, by
    filter_upwards [hS] with v hv
    simp only [hv, ↓reduceIte]
    exact (stdStab Q v).one_mem⟩

open Classical in
private theorem kEltGen_pos {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)
    (γ : orthGroup Q F) (S : HeightOneSpectrum (𝓞 F) → Prop)
    (hS : ∀ᶠ v in Filter.cofinite, ¬ S v) {v : HeightOneSpectrum (𝓞 F)} (h : S v) :
    ((kEltGen Q γ S hS v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) =
      GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (γ : GL (Fin n) F) := by
  change ((if S v then orthMap Q (v.adicCompletion F) γ else 1 : orthGroup Q (v.adicCompletion F)) :
    GL (Fin n) (v.adicCompletion F)) = _
  simp only [h, ↓reduceIte]
  rfl

open Classical in
private theorem kEltGen_neg {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)
    (γ : orthGroup Q F) (S : HeightOneSpectrum (𝓞 F) → Prop)
    (hS : ∀ᶠ v in Filter.cofinite, ¬ S v) {v : HeightOneSpectrum (𝓞 F)} (h : ¬ S v) :
    ((kEltGen Q γ S hS v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) = 1 := by
  change ((if S v then orthMap Q (v.adicCompletion F) γ else 1 : orthGroup Q (v.adicCompletion F)) :
    GL (Fin n) (v.adicCompletion F)) = _
  simp only [h, ↓reduceIte]
  rfl

open Classical in
private theorem kEltGen_mem {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)
    {γ : orthGroup Q F} (hγ : γ ∈ spinorKernel Q F) (S : HeightOneSpectrum (𝓞 F) → Prop)
    (hS : ∀ᶠ v in Filter.cofinite, ¬ S v) : kEltGen Q γ S hS ∈ spinorKernelAf Q := by
  intro v
  change (if S v then orthMap Q (v.adicCompletion F) γ else 1) ∈ spinorKernel Q (v.adicCompletion F)
  by_cases h : S v
  · simp only [h, ↓reduceIte]; exact orthMap_mem_spinorKernel Q v hγ
  · simp only [h, ↓reduceIte]; exact (spinorKernel Q _).one_mem

private theorem kHyp : ∀ᶠ v in Filter.cofinite, ¬ ((2 : 𝓞 ℚ) ∈ (v : HeightOneSpectrum (𝓞 ℚ)).asIdeal) :=
  eventually_not_mem (F := ℚ) (d := (2 : 𝓞 ℚ)) (by norm_num)

/-- The adele equal to $\varphi$ at the primes above $2$ and $1$ elsewhere. -/
private def kElt : OAf omeara104_6Form :=
  kEltGen omeara104_6Form phi (fun v => (2 : 𝓞 ℚ) ∈ v.asIdeal) kHyp

private theorem kElt_mem : kElt ∈ spinorKernelAf omeara104_6Form :=
  kEltGen_mem _ phi_mem _ kHyp

private theorem K_eq : omeara104_6K = latSMul omeara104_6Form kElt omeara104_6L := by
  apply Lat.ext
  apply loc_injective omeara104_6K.2 (latSMul _ kElt _).2
  intro v
  rw [loc_latSMul, show omeara104_6K.1 = glImage omeara104_6P intVec from rfl,
    show omeara104_6L.1 = intVec from rfl, loc_glImage, loc_intVec]
  by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · rw [kElt, kEltGen_pos _ _ _ kHyp h2]
    conv_lhs => rw [P_eq]
    exact locAct_mul_unit v _ _ (Uq_int v h2).1 (Uq_int v h2).2
  · rw [kElt, kEltGen_neg _ _ _ kHyp h2, locAct_one]
    have := locAct_mul_unit v 1 omeara104_6P (P_int v h2).1 (P_int v h2).2
    rwa [one_mul, map_one, locAct_one] at this

/-- **Example 104:6** (O'Meara 1973, §104, pp. 319–320): on the hyperbolic plane $V$ with $Q(a, b) = 18ab + 2b^2$,
the lattice $K = \mathbb Z\,\tfrac14x + \mathbb Z\,4y$ lies in the proper spinor genus of $L = \mathbb Z^2$ but not in
its class (so not in its proper class). The matrices are reconstructed (module docstring). -/
@[kb "omeara1963" "§104, 104:6, pp. 319–320 (matrices reconstructed: m = 9)"]
theorem omeara104_6 :
    omeara104_6Form.Nondegenerate ∧ omeara104_6Form.IsotropicIn ℚ ∧
      SameProperSpinorGenus omeara104_6Form omeara104_6L omeara104_6K ∧
      ¬ IsIsometric omeara104_6Form omeara104_6L.1 omeara104_6K.1 ∧
      ¬ IsProperIsometric omeara104_6Form omeara104_6L.1 omeara104_6K.1 := by
  refine ⟨f_nondeg, f_iso, ?_, not_isometric, fun h => not_isometric h.isIsometric⟩
  rw [sameProperSpinorGenus_iff]
  refine ⟨1, (Tamagawa.soSub omeara104_6Form ℚ).one_mem, kElt, kElt_mem, ?_⟩
  rw [diagF_smul, ← K_eq]
  apply Lat.ext
  change omeara104_6K.1 = glImage _ omeara104_6K.1
  rw [OneMemClass.coe_one, glImage_one]

end QuadFormsKB.Lattices
