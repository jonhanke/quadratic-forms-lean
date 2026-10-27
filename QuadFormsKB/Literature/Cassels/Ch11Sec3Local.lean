/-
# Cassels, Chapter 11, §3: spinor norms of non-dyadic local lattices (Lemmas 3.3 and 3.7)

**Layer:** $V_\mathfrak p = F_\mathfrak p^n$ at a finite prime $\mathfrak p \nmid 2$ of a number field $F$ (Cassels:
$\mathbb Q_p$, $p \ne 2$), with $Q$ = `Q : QuadForm F n`; a lattice $L$ = `L : Lat F n` and its localization
$\Lambda_p = L_\mathfrak p$ = `loc v L.1`; $\theta(\Lambda_p) = \theta(O^+(L_\mathfrak p))$ = `localSpinorNormGroup`
(`Literature/OMeara/Sec101D.lean`); the unit square classes `IsUnitSqClass`.

*Bases of local lattices.* A $\mathbb Z_p$-basis $b_1, \dots, b_n$ of $\Lambda_p$ is given as the columns of a matrix
$\gamma \in \mathrm{GL}_n(F_\mathfrak p)$ with $L_\mathfrak p = \gamma\,\mathfrak o_\mathfrak p^n$; the matrix of the
bilinear form $B(x, y) = Q(x+y) - Q(x) - Q(y)$ on this basis is $\gamma^{t}H\gamma$, with $H$ the Hessian of $Q$
(`qbil`). Cassels' $\phi(x, y)$ is $\tfrac12B(x,y)$; since $2$ is a unit at $\mathfrak p$, "the determinant of the form
induced on $\Lambda_p$ is a unit" is $\lvert\det(\gamma^tH\gamma)\rvert = 1$, and Cassels' determinant $d$ and
$\det(\gamma^tH\gamma)$ have the same valuation.

**Proves**
* Lemma 3.3 (p. 208): for $\mathfrak p \nmid 2$, $n \ge 2$, $Q$ integral on $\Lambda_p$ with unit determinant:
  $\theta(\Lambda_p) = U_p(\mathbb Q_p^\times)^2$ (`mem_localSpinorNormGroup_iff_of_unimodular`).
* Lemma 3.7 (p. 213), with the remark before it on direct orthogonal summands: if $\Lambda_p$ has an orthogonal basis
  with two vectors $b_i, b_j$ ($i \ne j$) of equal $\lvert\phi(b_i)\rvert_p = \lvert\phi(b_j)\rvert_p$, then
  $U_p \subseteq \theta(\Lambda_p)$ (`units_mem_localSpinorNormGroup_of_orthogonal`).
* Lemma 3.7, Corollary (p. 214): if $Q$ is integral on $\Lambda_p$ and $U_p \not\subseteq \theta(\Lambda_p)$, then
  $p^{n(n-1)/2}$ divides the determinant of $\Lambda_p$ (`valued_det_le_of_not_units_mem`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec1
import QuadFormsKB.Lattices.SpinorLocal
import QuadFormsKB.LocalDensity.DVR

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- The Gram matrix $\gamma^tH\gamma$ of the bilinear form $B$ on the basis given by the columns of $\gamma$. -/
def locGram (γ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv :=
  (γ : Matrix (Fin n) (Fin n) Fv)ᵀ * Q.hessian.map (algebraMap F Fv) * (γ : Matrix (Fin n) (Fin n) Fv)

/-! ### Coordinates and the Gram matrix -/

section Aux

variable {Q v}

local notation "𝔬" => v.adicCompletionIntegers F

/-- $B(\gamma c, \gamma d) = c^t G d$ for the Gram matrix $G = \gamma^tH\gamma$. -/
theorem qbil_mulVec_locGram (γ : GL (Fin n) Fv) (c d : Fin n → Fv) :
    qbil Q Fv (γ.val *ᵥ c) (γ.val *ᵥ d) = c ⬝ᵥ (locGram Q v γ *ᵥ d) := by
  unfold qbil locGram
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec c, vecMul_transpose]

theorem locGram_apply_eq (γ : GL (Fin n) Fv) (k l : Fin n) :
    qbil Q Fv (γ.val *ᵥ Pi.single k 1) (γ.val *ᵥ Pi.single l 1) = locGram Q v γ k l := by
  rw [qbil_mulVec_locGram]
  simp

/-- $2Q(\gamma c) = c^tGc$. -/
theorem two_mul_evalIn_locGram (γ : GL (Fin n) Fv) (c : Fin n → Fv) :
    2 * Q.evalIn Fv (γ.val *ᵥ c) = c ⬝ᵥ (locGram Q v γ *ᵥ c) := by
  rw [← qbil_self, qbil_mulVec_locGram]

theorem locGram_transpose (γ : GL (Fin n) Fv) : (locGram Q v γ)ᵀ = locGram Q v γ := by
  unfold locGram
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map,
    QuadForm.hessian_transpose, Matrix.mul_assoc]

theorem locGram_det (γ : GL (Fin n) Fv) :
    (locGram Q v γ).det = (γ.val.det) ^ 2 * (algebraMap F Fv Q.hessian.det) := by
  unfold locGram
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (Q.hessian.map (algebraMap F Fv)).det = algebraMap F Fv Q.hessian.det from
      (RingHom.map_det (algebraMap F Fv) Q.hessian).symm]
  ring

theorem locGram_det_ne_zero (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) : (locGram Q v γ).det ≠ 0 := by
  rw [locGram_det]
  refine mul_ne_zero (pow_ne_zero _ ?_) ?_
  · exact (Matrix.isUnits_det_units γ).ne_zero
  · exact (map_ne_zero_iff _ (algebraMap F Fv).injective).mpr hQ

theorem locGram_mul (γ P : GL (Fin n) Fv) :
    locGram Q v (γ * P) = (P.val)ᵀ * locGram Q v γ * P.val := by
  unfold locGram
  simp only [Units.val_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem qbil_le_one_of_int {M : Submodule 𝔬 (Fin n → Fv)} (hint : ∀ x ∈ M, Valued.v (Q.evalIn Fv x) ≤ 1)
    {x y : Fin n → Fv} (hx : x ∈ M) (hy : y ∈ M) : Valued.v (qbil Q Fv x y) ≤ 1 := by
  rw [qbil_eq_polar]
  exact Valuation.map_sub_le _ (Valuation.map_sub_le _ (hint _ (M.add_mem hx hy)) (hint _ hx)) (hint _ hy)

theorem valued_two (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Valued.v (2 : Fv) = 1 := by
  have hu : IsUnit (2 : 𝔬) :=
    LocalDensity.DVR.dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) (LocalDensity.NF.π_not_dvd_two v h2)
  have := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu
  rwa [show ((2 : 𝔬) : Fv) = 2 from rfl] at this

theorem mem_std_iff {d : Fin n → Fv} : d ∈ std v ↔ ∀ i, Valued.v (d i) ≤ 1 := by
  constructor
  · intro h i
    have := h i
    rwa [neg_zero, exp_zero] at this
  · intro h i
    rw [neg_zero, exp_zero]
    exact h i

theorem single_mem_std (i : Fin n) {s : Fv} (hs : Valued.v s ≤ 1) : (Pi.single i s : Fin n → Fv) ∈ std v := by
  rw [mem_std_iff]
  intro k
  by_cases hk : k = i
  · subst hk; simpa using hs
  · simp [hk]

/-- A symmetry $\tau_x$, $x \in M$, with $\lvert B(x, y)\rvert \le \lvert Q(x)\rvert$ for all $y \in M$ stabilizes
the $\mathfrak o_\mathfrak p$-module $M$ (the argument of `exists_symm_locAct_eq`). -/
theorem locAct_symm_eq {M : Submodule 𝔬 (Fin n → Fv)} {x : Fin n → Fv} (hxM : x ∈ M)
    (hx0 : Q.evalIn Fv x ≠ 0)
    (hb : ∀ y ∈ M, Valued.v (qbil Q Fv x y) ≤ Valued.v (Q.evalIn Fv x)) :
    locAct v (symm Q Fv x : GL (Fin n) Fv) M = M := by
  have hQx : Valued.v (Q.evalIn Fv x) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hmaps : ∀ y ∈ M, ((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y ∈ M := by
    intro y hy
    rw [symm_mulVec_bil Q Fv hx0]
    have hc : Valued.v (qbil Q Fv x y / Q.evalIn Fv x) ≤ 1 := by
      rw [map_div₀, div_eq_mul_inv, ← mul_inv_cancel₀ hQx]
      exact mul_le_mul_left (hb y hy) _
    have hcx : (qbil Q Fv x y / Q.evalIn Fv x) • x ∈ M :=
      M.smul_mem (⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩ : 𝔬) hxM
    exact M.sub_mem hy hcx
  refine le_antisymm ?_ fun y hy => ⟨_, hmaps y hy, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hmaps y hy
  · show ((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ
      (((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, symm_mul_self]
    simp

theorem locGram_mulVec_diag {γ : GL (Fin n) Fv} (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0)
    (d : Fin n → Fv) (k : Fin n) : (locGram Q v γ *ᵥ d) k = locGram Q v γ k k * d k := by
  rw [mulVec, dotProduct, Finset.sum_eq_single k]
  · intro l _ hl
    rw [horth k l hl.symm, zero_mul]
  · simp

theorem locGram_ne_zero_of_diag (hQ : Q.Nondegenerate) {γ : GL (Fin n) Fv}
    (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0) (i : Fin n) : locGram Q v γ i i ≠ 0 := by
  intro h0
  refine locGram_det_ne_zero hQ γ (Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_)
  by_cases hj : j = i
  · subst hj; exact h0
  · exact horth i j (Ne.symm hj)

theorem sqClassOf_mul_sq (u : Fvˣ) {r : Fv} (hr : r ≠ 0) : sqClassOf ((u : Fv) * r ^ 2) = SqClass.mk u := by
  rw [sqClassOf_mul u.ne_zero (pow_ne_zero 2 hr), (sqClassOf_eq_one_iff (pow_ne_zero 2 hr)).mpr ⟨r, sq r⟩,
    mul_one, sqClassOf_of_ne_zero u.ne_zero]
  exact congrArg SqClass.mk (Units.ext rfl)

/-- **Two symmetries in $O(L_\mathfrak p)$ give an element of $\theta(O^+(L_\mathfrak p))$.** -/
theorem mem_localSpinorNormGroup_of_symm_pair (hQ : Q.Nondegenerate) (L : Lat F n) {x y : Fin n → Fv}
    (hx0 : Q.evalIn Fv x ≠ 0) (hy0 : Q.evalIn Fv y ≠ 0) (hxs : symm Q Fv x ∈ locStabV Q v L)
    (hys : symm Q Fv y ∈ locStabV Q v L) (a : Fvˣ)
    (ha : sqClassOf (Q.evalIn Fv x * Q.evalIn Fv y) = SqClass.mk a) : a ∈ localSpinorNormGroup Q hQ v L := by
  rw [mem_localSpinorNormGroup]
  refine ⟨symm Q Fv x * symm Q Fv y, ⟨(locStabV Q v L).mul_mem hxs hys, ?_⟩, ?_⟩
  · refine Tamagawa.mem_soSub.mpr ?_
    change (((symm Q Fv x : GL (Fin n) Fv) * (symm Q Fv y : GL (Fin n) Fv) : GL (Fin n) Fv) :
      Matrix (Fin n) (Fin n) Fv).det = 1
    rw [Units.val_mul, Matrix.det_mul, symm_det Q Fv hx0, symm_det Q Fv hy0]
    norm_num
  · have := spinorNorm_symmProd Q Fv hQ [x, y] (by simp [hx0, hy0])
    simp only [symmProd, valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    rw [this, ha]

/-- **The symmetries of a pair of orthogonal basis vectors:** if $b_i, b_j$ ($i \ne j$) are orthogonal basis vectors
of $L_\mathfrak p$ with $\lvert B(b_i,b_i)\rvert = \lvert B(b_j,b_j)\rvert$, then every $w \ne 0$ of that absolute value
is $2Q(x)$ for some $x \in \mathfrak o b_i + \mathfrak o b_j$ with $\tau_x \in O(L_\mathfrak p)$ ($\mathfrak p \nmid 2$). -/
theorem exists_symm_pair (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F n) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0) {i j : Fin n}
    (hij : i ≠ j) (hv : Valued.v (locGram Q v γ i i) = Valued.v (locGram Q v γ j j)) {w : Fv}
    (hw : Valued.v w = Valued.v (locGram Q v γ i i)) (hw0 : w ≠ 0) :
    ∃ x, Q.evalIn Fv x = w / 2 ∧ symm Q Fv x ∈ locStabV Q v L := by
  set a := locGram Q v γ i i with ha
  set b := locGram Q v γ j j with hb
  have hvw : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw0
  have ha0 : a ≠ 0 := fun h => hvw (by rw [hw, h, map_zero])
  have hb0 : b ≠ 0 := fun h => hvw (by rw [hw, hv, h, map_zero])
  have hA : Valued.v (a / w) = 1 := by rw [map_div₀, hw, div_self ((Valuation.ne_zero_iff _).mpr ha0)]
  have hB : Valued.v (b / w) = 1 := by rw [map_div₀, hw, ← hv, div_self ((Valuation.ne_zero_iff _).mpr ha0)]
  have hAu : IsUnit (toO v (a / w) hA.le) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hA
  have hBu : IsUnit (toO v (b / w) hB.le) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hB
  obtain ⟨s, t, hst⟩ := Nbr.exists_binary_one_dvr (LocalDensity.NF.irreducible_π v)
    (LocalDensity.NF.π_not_dvd_two v h2) hAu hBu
  have hst' : a * (s : Fv) ^ 2 + b * (t : Fv) ^ 2 = w := by
    have := congrArg (fun z : 𝔬 => (z : Fv)) hst
    push_cast at this
    change a / w * (s : Fv) ^ 2 + b / w * (t : Fv) ^ 2 = 1 at this
    field_simp at this
    linear_combination this
  set c : Fin n → Fv := Pi.single i (s : Fv) + Pi.single j (t : Fv) with hc
  have hci : c i = s := by simp [hc, hij]
  have hcj : c j = t := by simp [hc, hij.symm]
  have hs1 : Valued.v (s : Fv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp s.2
  have ht1 : Valued.v (t : Fv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2
  have hcstd : c ∈ std v := (std v).add_mem (single_mem_std i hs1) (single_mem_std j ht1)
  have h2v : Valued.v (2 : Fv) = 1 := valued_two h2
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hQx : Q.evalIn Fv (γ.val *ᵥ c) = w / 2 := by
    have := two_mul_evalIn_locGram (Q := Q) (v := v) γ c
    rw [hc, add_dotProduct, single_dotProduct, single_dotProduct, locGram_mulVec_diag horth,
      locGram_mulVec_diag horth, ← hc, hci, hcj] at this
    rw [eq_div_iff h2ne, mul_comm, this]
    linear_combination hst'
  refine ⟨γ.val *ᵥ c, hQx, ?_⟩
  have hxM : γ.val *ᵥ c ∈ loc v L.1 := by rw [hγ]; exact ⟨c, hcstd, rfl⟩
  have hx0 : Q.evalIn Fv (γ.val *ᵥ c) ≠ 0 := by rw [hQx]; exact div_ne_zero hw0 h2ne
  show locAct v (symm Q Fv (γ.val *ᵥ c) : GL (Fin n) Fv) (loc v L.1) = loc v L.1
  refine locAct_symm_eq hxM hx0 fun y hy => ?_
  rw [hγ, mem_locAct] at hy
  obtain ⟨d, hd, rfl⟩ := hy
  rw [qbil_mulVec_locGram, hc, add_dotProduct, single_dotProduct, single_dotProduct, locGram_mulVec_diag horth,
    locGram_mulVec_diag horth, hQx, map_div₀, h2v, div_one, hw]
  have hd' := mem_std_iff.mp hd
  have h1 : Valued.v ((s : Fv) * (a * d i)) ≤ Valued.v a := by
    rw [map_mul, map_mul]
    calc _ ≤ 1 * (Valued.v a * 1) := mul_le_mul' hs1 (mul_le_mul' le_rfl (hd' i))
      _ = _ := by simp
  have h2' : Valued.v ((t : Fv) * (b * d j)) ≤ Valued.v a := by
    rw [map_mul, map_mul, ← hv]
    calc _ ≤ 1 * (Valued.v a * 1) := mul_le_mul' ht1 (mul_le_mul' le_rfl (hd' j))
      _ = _ := by simp
  exact Valuation.map_add_le _ h1 h2'

open LocalDensity in
/-- **A diagonal basis of an integral local lattice** ($\mathfrak p \nmid 2$): there is a basis $\gamma'$ of $L_\mathfrak p$
whose Gram matrix is diagonal with entries of absolute value $\lvert\varpi\rvert^{\nu_k}$, $\nu_k \in \mathbb N$, and
the same $\lvert\det\rvert$ as that of $\gamma$ (Jordan decomposition over $\mathfrak o_\mathfrak p$, `dvr_jinv_complete_aux`). -/
theorem exists_diag_basis (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F n)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1) :
    ∃ (γ' : GL (Fin n) Fv) (ν : Fin n → ℕ), loc v L.1 = locAct v γ' (std v) ∧
      (∀ k l, k ≠ l → locGram Q v γ' k l = 0) ∧
      (∀ k, Valued.v (locGram Q v γ' k k) = exp (-(ν k : ℤ))) ∧
      Valued.v (locGram Q v γ').det = Valued.v (locGram Q v γ).det := by
  classical
  have hmemb : ∀ k, γ.val *ᵥ Pi.single k 1 ∈ loc v L.1 := fun k => by
    rw [hγ, mem_locAct]; exact ⟨_, single_mem_std k (by simp), rfl⟩
  have hle : ∀ k l, Valued.v (locGram Q v γ k l) ≤ 1 := fun k l => by
    rw [← locGram_apply_eq]; exact qbil_le_one_of_int hint (hmemb k) (hmemb l)
  let G₀ : Matrix (Fin n) (Fin n) 𝔬 := Matrix.of fun k l => toO v _ (hle k l)
  have hG₀ : G₀.map (algebraMap 𝔬 Fv) = locGram Q v γ := by ext k l; rfl
  have hinj : Function.Injective (algebraMap 𝔬 Fv) := fun a b h => Subtype.ext h
  have hsymm : G₀ᵀ = G₀ := by
    refine Matrix.map_injective hinj ?_
    show G₀ᵀ.map (algebraMap 𝔬 Fv) = G₀.map (algebraMap 𝔬 Fv)
    rw [Matrix.transpose_map, hG₀, locGram_transpose]
  have hπ := NF.irreducible_π v
  have hπ2 : ¬ NF.π v ∣ 2 := NF.π_not_dvd_two v h2
  have hu2 : IsUnit (2 : 𝔬) := DVR.dvr_isUnit_of_not_dvd hπ hπ2
  obtain ⟨u2, hu2'⟩ := hu2
  set e : 𝔬 := ((u2⁻¹ : 𝔬ˣ) : 𝔬) with he
  have he2 : e + e = 1 := by
    have : e * (u2 : 𝔬) = 1 := by rw [he]; exact u2.inv_mul
    rw [hu2'] at this
    linear_combination this
  set c : Matrix (Fin n) (Fin n) 𝔬 := e • G₀ with hc
  have hcc : c + cᵀ = G₀ := by
    rw [hc, Matrix.transpose_smul, hsymm, ← add_smul, he2, one_smul]
  have hdet0 : (c + cᵀ).det ≠ 0 := by
    rw [hcc]
    intro h
    apply locGram_det_ne_zero hQ γ
    rw [← hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  have hJ0 : DVR.DvrJInv (NF.π v) (c + cᵀ) ∅ ∅ (fun _ => 0) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i j _ h
    simp at h
  have h2' : ¬ NF.π v ^ 2 ∣ 2 := fun h => hπ2 (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  obtain ⟨V, P', ν', hV, hJ⟩ := DVR.dvr_jinv_complete_aux hπ h2' _ c ∅ ∅ (fun _ => 0) rfl hdet0 hJ0
  have hP' : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hne => hπ2 (hJ.1 hne)
  subst hP'
  rw [hcc] at hJ
  let Pg : GL (Fin n) 𝔬 := Matrix.nonsingInvUnit V hV
  let P : GL (Fin n) Fv := GeneralLinearGroup.map (algebraMap 𝔬 Fv) Pg
  have hPval : P.val = V.map (algebraMap 𝔬 Fv) := rfl
  have H1 : locGram Q v (γ * P) = (Vᵀ * G₀ * V).map (algebraMap 𝔬 Fv) := by
    rw [locGram_mul, hPval, ← hG₀]
    simp [Matrix.map_mul, Matrix.transpose_map]
  refine ⟨γ * P, ν', ?_, ?_, ?_, ?_⟩
  · rw [locAct_mul, locAct_map_std v Pg, ← hγ]
  · intro k l hkl
    rw [H1, Matrix.map_apply]
    have := hJ.2.2.2.1 k l hkl (Or.inl (Finset.mem_univ _)) (by simp) (by simp)
    rw [this, map_zero]
  · intro k
    obtain ⟨u, hu, hunit⟩ := hJ.2.2.2.2.2 k (Finset.mem_univ _) (by simp [LocalDensity.IsPaired])
    rw [H1, Matrix.map_apply, hu]
    have hu1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hunit
    have h2v := valued_two h2
    have hpv := NF.valued_π v
    have hc : algebraMap 𝔬 Fv (2 * NF.π v ^ ν' k * u) = 2 * ((NF.π v : 𝔬) : Fv) ^ ν' k * (u : Fv) := by
      rw [map_mul, map_mul, map_pow]
      rfl
    rw [hc, map_mul, map_mul, map_pow, h2v, hpv, hu1, one_mul, mul_one, ← WithZero.exp_nsmul]
    congr 1
    simp
  · rw [locGram_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul]
    have : Valued.v (P.val.det) = 1 := by
      rw [hPval, show (V.map (algebraMap 𝔬 Fv)).det = algebraMap 𝔬 Fv V.det from
        (RingHom.map_det (algebraMap 𝔬 Fv) V).symm]
      exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hV
    rw [this]
    simp

/-- $n$ distinct natural numbers sum to at least $0 + 1 + \dots + (n-1)$. -/
theorem sum_range_le_sum_finset (S : Finset ℕ) : ∑ i ∈ Finset.range S.card, i ≤ ∑ s ∈ S, s := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have han : a ∉ s := fun h => lt_irrefl _ (ha a h)
    rw [Finset.card_insert_of_notMem han, Finset.sum_range_succ, Finset.sum_insert han]
    have : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (ha x hx)
      simpa using Finset.card_le_card this
    omega

theorem sum_range_le_sum_of_injective (ν : Fin n → ℕ) (hν : Function.Injective ν) :
    ∑ i ∈ Finset.range n, i ≤ ∑ k, ν k := by
  have := sum_range_le_sum_finset (Finset.univ.image ν)
  rwa [Finset.card_image_of_injective _ hν, Finset.card_univ, Fintype.card_fin,
    Finset.sum_image (fun a _ b _ h => hν h)] at this

theorem prod_exp {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, (exp (f i) : WithZero (Multiplicative ℤ)) = exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, exp_add]

/-- The subgroup of unit square classes $\mathfrak o_\mathfrak p^\times F_\mathfrak p^{\times 2}/F_\mathfrak p^{\times 2}$. -/
def unitSqSubgroup : Subgroup (SqClass Fv) where
  carrier := {c | IsUnitSqClass v c}
  mul_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hu; exact zero_ne_one hu
    have hu0' : u' ≠ 0 := fun h => by rw [h, map_zero] at hu'; exact zero_ne_one hu'
    exact ⟨u * u', by rw [map_mul, hu, hu', one_mul], (sqClassOf_mul hu0 hu0').symm⟩
  one_mem' := ⟨1, map_one _, sqClassOf_one.symm⟩
  inv_mem' := by
    intro c hc
    rwa [SqClass.inv_eq]

theorem coe_mul_mulVec (a b : orthGroup Q Fv) (x : Fin n → Fv) :
    ((a * b : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ x =
      (a : GL (Fin n) Fv).val *ᵥ ((b : GL (Fin n) Fv).val *ᵥ x) := by
  rw [Matrix.mulVec_mulVec]; rfl

/-- The generating set of symmetries $\tau_z$, $z \in L_\mathfrak p$ with $Q(z)$ a unit. -/
def unitSymmSet (L : Lat F n) : Set (orthGroup Q Fv) :=
  {τ | ∃ z ∈ loc v L.1, Valued.v (Q.evalIn Fv z) = 1 ∧ τ = symm Q Fv z}

theorem symm_mem_locStabV_of_unit (L : Lat F n)
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1) {z : Fin n → Fv} (hz : z ∈ loc v L.1)
    (hQz : Valued.v (Q.evalIn Fv z) = 1) : symm Q Fv z ∈ locStabV Q v L := by
  have hz0 : Q.evalIn Fv z ≠ 0 := fun h => by rw [h, map_zero] at hQz; exact zero_ne_one hQz
  show locAct v (symm Q Fv z : GL (Fin n) Fv) (loc v L.1) = loc v L.1
  exact locAct_symm_eq hz hz0 fun y hy => by rw [hQz]; exact qbil_le_one_of_int hint hz hy

theorem parallelogram (x y : Fin n → Fv) :
    Q.evalIn Fv (x + y) + Q.evalIn Fv (x - y) = 2 * Q.evalIn Fv x + 2 * Q.evalIn Fv y := by
  apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
  have e1 := two_mul_evalIn_eq Q Fv x
  have e2 := two_mul_evalIn_eq Q Fv y
  have e3 := two_mul_evalIn_eq Q Fv (x + y)
  have e4 := two_mul_evalIn_eq Q Fv (x - y)
  simp only [qbil_add_left, qbil_add_right] at e3
  simp only [qbil_sub_left, qbil_sub_right] at e4
  have e5 := qbil_comm Q Fv y x
  linear_combination e3 + e4 - 2 * e1 - 2 * e2

/-- **One step of the factorization into unit symmetries:** if $\sigma \in O(L_\mathfrak p)$ fixes the orthogonal
basis vectors $b_l$ for $l < k$, there is a product $\rho$ of at most two unit symmetries in $O(L_\mathfrak p)$ such
that $\rho\sigma$ fixes $b_l$ for $l \le k$. -/
theorem exists_fix_step (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F n) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0)
    (hunit : ∀ k, Valued.v (locGram Q v γ k k) = 1) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (k : Fin n) (σ : orthGroup Q Fv) (hσ : σ ∈ locStabV Q v L)
    (hfix : ∀ l : Fin n, l < k →
      (σ : GL (Fin n) Fv).val *ᵥ (γ.val *ᵥ Pi.single l 1) = γ.val *ᵥ Pi.single l 1) :
    ∃ ρ ∈ Subgroup.closure (unitSymmSet (Q := Q) (v := v) L), ρ ∈ locStabV Q v L ∧
      ∀ l : Fin n, l ≤ k →
        ((ρ * σ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ (γ.val *ᵥ Pi.single l 1) = γ.val *ᵥ Pi.single l 1 := by
  have h2v : Valued.v (2 : Fv) = 1 := valued_two h2
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  set b : Fin n → Fv := γ.val *ᵥ Pi.single k 1 with hb
  set w : Fin n → Fv := (σ : GL (Fin n) Fv).val *ᵥ b with hw
  have hmem : ∀ l, γ.val *ᵥ Pi.single l 1 ∈ loc v L.1 := fun l => by
    rw [hγ, mem_locAct]; exact ⟨_, single_mem_std l (by simp), rfl⟩
  have hbM : b ∈ loc v L.1 := hmem k
  have hσ' : locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 := hσ
  have hwM : w ∈ loc v L.1 := by
    rw [← hσ', mem_locAct]; exact ⟨b, hbM, rfl⟩
  have hQw : Q.evalIn Fv w = Q.evalIn Fv b := by
    apply mul_left_cancel₀ h2ne
    rw [two_mul_evalIn_eq, two_mul_evalIn_eq, hw]
    exact qbil_orth Q Fv σ b b
  have hQb : Valued.v (Q.evalIn Fv b) = 1 := by
    have : 2 * Q.evalIn Fv b = locGram Q v γ k k := by
      rw [two_mul_evalIn_eq, hb, locGram_apply_eq]
    have h := hunit k
    rw [← this, map_mul, h2v, one_mul] at h
    exact h
  have hbl : ∀ l : Fin n, l < k → qbil Q Fv b (γ.val *ᵥ Pi.single l 1) = 0 := fun l hl => by
    rw [hb, locGram_apply_eq]; exact horth k l (ne_of_gt hl)
  have hwl : ∀ l : Fin n, l < k → qbil Q Fv w (γ.val *ᵥ Pi.single l 1) = 0 := fun l hl => by
    rw [hw]
    conv_lhs => rw [← hfix l hl]
    rw [qbil_orth Q Fv σ b _, hbl l hl]
  have hsymm_fix : ∀ z : Fin n → Fv, (∀ l : Fin n, l < k → qbil Q Fv z (γ.val *ᵥ Pi.single l 1) = 0) →
      ∀ l : Fin n, l < k →
        (symm Q Fv z : GL (Fin n) Fv).val *ᵥ (γ.val *ᵥ Pi.single l 1) = γ.val *ᵥ Pi.single l 1 :=
    fun z hz l hl => symm_fix Q Fv (hz l hl)
  have hbS : symm Q Fv b ∈ Subgroup.closure (unitSymmSet (Q := Q) (v := v) L) :=
    Subgroup.subset_closure ⟨b, hbM, hQb, rfl⟩
  by_cases hA : Valued.v (Q.evalIn Fv (b - w)) = 1
  · have hz0 : Q.evalIn Fv (b - w) ≠ 0 := fun h => by rw [h, map_zero] at hA; exact zero_ne_one hA
    have hzM : b - w ∈ loc v L.1 := (loc v L.1).sub_mem hbM hwM
    refine ⟨symm Q Fv (b - w), Subgroup.subset_closure ⟨b - w, hzM, hA, rfl⟩,
      symm_mem_locStabV_of_unit L hint hzM hA, fun l hl => ?_⟩
    rw [coe_mul_mulVec]
    rcases hl.lt_or_eq with hl | rfl
    · rw [hfix l hl]
      exact hsymm_fix (b - w) (fun l hl => by rw [qbil_sub_left, hbl l hl, hwl l hl, sub_zero]) l hl
    · rw [← hb, ← hw]
      exact symm_sub_apply Q Fv hQw.symm hz0
  · have hlt : Valued.v (Q.evalIn Fv (b - w)) < 1 :=
      lt_of_le_of_ne (hint _ ((loc v L.1).sub_mem hbM hwM)) hA
    have hB : Valued.v (Q.evalIn Fv (b + w)) = 1 := by
      by_contra hB
      have hlt' : Valued.v (Q.evalIn Fv (b + w)) < 1 :=
        lt_of_le_of_ne (hint _ ((loc v L.1).add_mem hbM hwM)) hB
      have hsum := Valuation.map_add_lt _ hlt' hlt
      rw [parallelogram, hQw, ← mul_add, map_mul, h2v, one_mul] at hsum
      have : Q.evalIn Fv b + Q.evalIn Fv b = 2 * Q.evalIn Fv b := by ring
      rw [this, map_mul, h2v, one_mul, hQb] at hsum
      exact lt_irrefl _ hsum
    have hz0 : Q.evalIn Fv (b + w) ≠ 0 := fun h => by rw [h, map_zero] at hB; exact zero_ne_one hB
    have hzM : b + w ∈ loc v L.1 := (loc v L.1).add_mem hbM hwM
    have hzS : symm Q Fv (b + w) ∈ Subgroup.closure (unitSymmSet (Q := Q) (v := v) L) :=
      Subgroup.subset_closure ⟨b + w, hzM, hB, rfl⟩
    refine ⟨symm Q Fv b * symm Q Fv (b + w), Subgroup.mul_mem _ hbS hzS,
      (locStabV Q v L).mul_mem (symm_mem_locStabV_of_unit L hint hbM hQb)
        (symm_mem_locStabV_of_unit L hint hzM hB), fun l hl => ?_⟩
    rw [mul_assoc, coe_mul_mulVec, coe_mul_mulVec]
    rcases hl.lt_or_eq with hl | rfl
    · rw [hfix l hl, hsymm_fix (b + w) (fun l hl => by rw [qbil_add_left, hbl l hl, hwl l hl, add_zero]) l hl,
        hsymm_fix b hbl l hl]
    · have hQb0 : Q.evalIn Fv b ≠ 0 := fun h => by rw [h, map_zero] at hQb; exact zero_ne_one hQb
      rw [← hb, ← hw, symm_add_apply Q Fv hQw.symm hz0, symm_mulVec_bil Q Fv hQb0]
      have : qbil Q Fv b (-b) = -(2 * Q.evalIn Fv b) := by
        rw [qbil_comm, qbil_neg_left, qbil_self]
      rw [this, show -(2 * Q.evalIn Fv b) / Q.evalIn Fv b = -2 by field_simp]
      module

/-- **Every element of $O(L_\mathfrak p)$ is a product of unit symmetries** when $L_\mathfrak p$ has an orthogonal basis
of unit-norm vectors. -/
theorem mem_closure_unitSymmSet (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F n) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0)
    (hunit : ∀ k, Valued.v (locGram Q v γ k k) = 1) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (σ : orthGroup Q Fv) (hσ : σ ∈ locStabV Q v L) :
    σ ∈ Subgroup.closure (unitSymmSet (Q := Q) (v := v) L) := by
  have key : ∀ d, d ≤ n → ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
      (∀ l : Fin n, l.val < n - d →
        (σ : GL (Fin n) Fv).val *ᵥ (γ.val *ᵥ Pi.single l 1) = γ.val *ᵥ Pi.single l 1) →
      σ ∈ Subgroup.closure (unitSymmSet (Q := Q) (v := v) L) := by
    intro d
    induction d with
    | zero =>
      intro _ σ _ hfix
      have h1 : (σ : GL (Fin n) Fv) * γ = γ := by
        refine Units.ext (Matrix.ext fun i l => ?_)
        have := congrFun (hfix l (by omega)) i
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
        exact this
      have : σ = 1 := by
        apply Subtype.ext
        exact (mul_left_inj γ).mp (h1.trans (one_mul γ).symm)
      rw [this]; exact Subgroup.one_mem _
    | succ d ih =>
      intro hd σ hσ hfix
      have hk : n - (d + 1) < n := by omega
      obtain ⟨ρ, hρS, hρ, hρfix⟩ := exists_fix_step h2 L γ hγ horth hunit hint ⟨n - (d + 1), hk⟩ σ hσ
        (fun l hl => hfix l (by simpa [Fin.lt_def] using hl))
      have hmem := ih (by omega) (ρ * σ) ((locStabV Q v L).mul_mem hρ hσ) (fun l hl => hρfix l (by
        rw [Fin.le_def]; simp only; omega))
      have : σ = ρ⁻¹ * (ρ * σ) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hρS) hmem
  exact key n le_rfl σ hσ (fun l hl => by omega)

end Aux

/-- **Cassels, Lemma 3.3** (Ch. 11, p. 208): *let $p \ne 2$ and $\Lambda^{(p)}$ a lattice in $V_p$; suppose that $\phi$
takes integral values on $\Lambda^{(p)}$ and that the determinant of the induced form is a $p$-adic unit. Then
$\theta(\Lambda^{(p)}) = U_p(\mathbb Q_p^\times)^2$* (for $n \ge 2$). Here $\Lambda^{(p)} = L_\mathfrak p =
\gamma\,\mathfrak o_\mathfrak p^n$ at a non-dyadic prime $\mathfrak p$ of a number field (every lattice on
$V_\mathfrak p$ is the localization of a lattice on $V$, Cassels' Theorem 1.1, `LocFamily.glue`). *Proof:*
"$\supseteq$": every unit is a value $Q(x)$, $x \in L_\mathfrak p$, and $\tau_x\tau_y \in O^+(L_\mathfrak p)$ for
$Q(x) = u$, $Q(y) = 1$; "$\subseteq$": $O(L_\mathfrak p)$ is generated by the symmetries $\tau_b$ with $b \in
L_\mathfrak p$, $Q(b)$ a unit (Cassels, Ch. 8, Lemma 3.3, Cor. 2). -/
@[kb "cassels1978" "Ch. 11, Lemma 3.3, p. 208 (over F_𝔭, 𝔭 ∤ 2)"]
theorem mem_localSpinorNormGroup_iff_of_unimodular (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hn : 2 ≤ n) (L : Lat F n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1) (hdet : Valued.v (locGram Q v γ).det = 1)
    (a : Fvˣ) : a ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk a) := by
  obtain ⟨γ', ν, hγ', horth, hval, hdet'⟩ := exists_diag_basis hQ h2 L γ hγ hint
  have hdet1 : Valued.v (locGram Q v γ').det = 1 := hdet'.trans hdet
  have hunit : ∀ k, Valued.v (locGram Q v γ' k k) = 1 := by
    have hG : locGram Q v γ' = Matrix.diagonal (fun k => locGram Q v γ' k k) := by
      ext k l
      by_cases h : k = l
      · subst h; simp
      · rw [horth k l h, Matrix.diagonal_apply_ne _ h]
    rw [hG, Matrix.det_diagonal, map_prod] at hdet1
    simp only [hval] at hdet1
    rw [prod_exp, ← exp_zero, exp_inj] at hdet1
    have h3 : (∑ k, ν k) = 0 := by
      have : (∑ k, -(ν k : ℤ)) = -((∑ k, ν k : ℕ) : ℤ) := by simp [Finset.sum_neg_distrib]
      omega
    intro k
    rw [hval k, (Finset.sum_eq_zero_iff.mp h3) k (Finset.mem_univ k)]
    simp
  constructor
  · intro h
    obtain ⟨σ, ⟨hσ, -⟩, hθ⟩ := (mem_localSpinorNormGroup Q hQ v L).mp h
    have hle : Subgroup.closure (unitSymmSet (Q := Q) (v := v) L) ≤
        (unitSqSubgroup (v := v)).comap (spinorNormHom Q Fv hQ) := by
      rw [Subgroup.closure_le]
      rintro τ ⟨z, hz, hQz, rfl⟩
      have hz0 : Q.evalIn Fv z ≠ 0 := fun h => by rw [h, map_zero] at hQz; exact zero_ne_one hQz
      show spinorNormHom Q Fv hQ (symm Q Fv z) ∈ unitSqSubgroup (v := v)
      rw [spinorNormHom_apply, spinorNorm_symm Q Fv hQ hz0]
      exact ⟨Q.evalIn Fv z, hQz, rfl⟩
    have := hle (mem_closure_unitSymmSet h2 L γ' hγ' horth hunit hint σ hσ)
    have h' : spinorNormHom Q Fv hQ σ ∈ unitSqSubgroup (v := v) := this
    rwa [spinorNormHom_apply, hθ] at h'
  · rintro ⟨u0, hu0, hmk⟩
    have hu00 : u0 ≠ 0 := fun h => by rw [h, map_zero] at hu0; exact zero_ne_one hu0
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    have heq : Valued.v (locGram Q v γ' i i) = Valued.v (locGram Q v γ' j j) := by rw [hunit, hunit]
    have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
    have h2v := valued_two h2
    obtain ⟨x₁, hx₁, hs₁⟩ := exists_symm_pair h2 L γ' hγ' horth hij heq (w := 2 * u0)
      (by rw [map_mul, h2v, hu0, mul_one, hunit]) (mul_ne_zero h2ne hu00)
    obtain ⟨x₂, hx₂, hs₂⟩ := exists_symm_pair h2 L γ' hγ' horth hij heq (w := 2)
      (by rw [h2v, hunit]) h2ne
    refine mem_localSpinorNormGroup_of_symm_pair hQ L (by rw [hx₁]; exact div_ne_zero (mul_ne_zero h2ne hu00) h2ne)
      (by rw [hx₂]; exact div_ne_zero h2ne h2ne) hs₁ hs₂ a ?_
    rw [hx₁, hx₂, show 2 * u0 / 2 * (2 / 2 : Fv) = u0 by field_simp]
    exact hmk.symm

/-- **Cassels, Lemma 3.7** (Ch. 11, p. 213), together with the remark before it (p. 213: $\theta(\Lambda') \subseteq
\theta(\Lambda)$ for a direct orthogonal summand $\Lambda'$ of $\Lambda$): *let $p \ne 2$ and let $\Lambda^{(p)}$ be a
$2$-dimensional lattice with a basis $b_1, b_2$ such that $\phi(x_1b_1 + x_2b_2) = a_1x_1^2 + a_2x_2^2$ with
$\lvert a_1\rvert_p = \lvert a_2\rvert_p$. Then $U_p \subseteq \theta(\Lambda^{(p)})$.* Here: if the basis
$b_1, \dots, b_n$ of $L_\mathfrak p$ (the columns of $\gamma$) is orthogonal and two of its vectors $b_i, b_j$,
$i \ne j$, have $\lvert Q(b_i)\rvert = \lvert Q(b_j)\rvert$, then every unit is in $\theta(O^+(L_\mathfrak p))$
($\mathfrak p \nmid 2$; the case $n = 2$ is Cassels' lemma). *Proof:* for a unit $u$ take $x = sb_i + tb_j$ with
$Q(x) = uQ(b_i)$ (the binary form $Q(b_i)s^2 + Q(b_j)t^2$ is a unit multiple of a unimodular form); then $\tau_x,
\tau_{b_i} \in O(L_\mathfrak p)$ and $\theta(\tau_x\tau_{b_i}) = uQ(b_i)^2$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.7 and the remark on direct orthogonal summands, p. 213 (over F_𝔭, 𝔭 ∤ 2)"]
theorem units_mem_localSpinorNormGroup_of_orthogonal (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (L : Lat F n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0) {i j : Fin n} (hij : i ≠ j)
    (heq : Valued.v (locGram Q v γ i i) = Valued.v (locGram Q v γ j j))
    (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) : u ∈ localSpinorNormGroup Q hQ v L := by
  have ha0 := locGram_ne_zero_of_diag hQ horth i
  have hua : Valued.v ((u : Fv) * locGram Q v γ i i) = Valued.v (locGram Q v γ i i) := by
    rw [map_mul, hu, one_mul]
  obtain ⟨x₁, hx₁, hs₁⟩ := exists_symm_pair h2 L γ hγ horth hij heq (w := (u : Fv) * locGram Q v γ i i) hua
    (mul_ne_zero u.ne_zero ha0)
  obtain ⟨x₂, hx₂, hs₂⟩ := exists_symm_pair h2 L γ hγ horth hij heq (w := locGram Q v γ i i) rfl ha0
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  refine mem_localSpinorNormGroup_of_symm_pair hQ L (by rw [hx₁]; exact div_ne_zero (mul_ne_zero u.ne_zero ha0) h2ne)
    (by rw [hx₂]; exact div_ne_zero ha0 h2ne) hs₁ hs₂ u ?_
  rw [hx₁, hx₂]
  have : (u : Fv) * locGram Q v γ i i / 2 * (locGram Q v γ i i / 2) = (u : Fv) * (locGram Q v γ i i / 2) ^ 2 := by
    ring
  rw [this]
  exact sqClassOf_mul_sq u (div_ne_zero ha0 h2ne)

/-- **Cassels, Lemma 3.7, Corollary** (Ch. 11, p. 214): *suppose that $\phi$ takes $p$-adic integral values on
$\Lambda_p$ and that $U_p \not\subseteq \theta(\Lambda_p)$. Then the determinant of $\Lambda_p$ is divisible by
$p^{n(n-1)/2}$* ($p \ne 2$). Here: for every basis of $L_\mathfrak p$ (the columns of $\gamma$),
$\lvert\det(\gamma^tH\gamma)\rvert \le \lvert\varpi\rvert^{n(n-1)/2}$, $\varpi$ a uniformizer ($\mathfrak p \nmid 2$).
*Proof:* diagonalize the form on $L_\mathfrak p$ over $\mathfrak o_\mathfrak p$ (Cassels, Ch. 8, Thm. 3.1); by Lemma
3.7 the $n$ diagonal entries have pairwise different valuations $\ge 0$, whose sum is at least
$0 + 1 + \dots + (n-1)$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.7, Cor., p. 214 (over F_𝔭, 𝔭 ∤ 2)"]
theorem valued_det_le_of_not_units_mem (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lat F n)
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (hnot : ¬ ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) :
    Valued.v (locGram Q v γ).det ≤ exp (-((n * (n - 1) / 2 : ℕ) : ℤ)) := by
  obtain ⟨γ', ν, hγ', horth, hval, hdet⟩ := exists_diag_basis hQ h2 L γ hγ hint
  rw [← hdet]
  have hinj : Function.Injective ν := by
    intro i j hij
    by_contra hne
    apply hnot
    intro u hu
    exact units_mem_localSpinorNormGroup_of_orthogonal Q v hQ h2 L γ' hγ' horth hne
      (by rw [hval, hval, hij]) u hu
  have hG : locGram Q v γ' = Matrix.diagonal (fun k => locGram Q v γ' k k) := by
    ext k l
    by_cases h : k = l
    · subst h; simp
    · rw [horth k l h, Matrix.diagonal_apply_ne _ h]
  rw [hG, Matrix.det_diagonal, map_prod]
  simp only [hval]
  rw [prod_exp, exp_le_exp]
  have h1 := sum_range_le_sum_of_injective ν hinj
  rw [Finset.sum_range_id] at h1
  have h3 : (∑ k, -(ν k : ℤ)) = -((∑ k, ν k : ℕ) : ℤ) := by
    simp [Finset.sum_neg_distrib]
  rw [h3]
  generalize n * (n - 1) / 2 = m at *
  omega

end QuadFormsKB.Lattices
