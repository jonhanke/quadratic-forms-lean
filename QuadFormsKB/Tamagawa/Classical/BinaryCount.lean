/-
# The number of representations by the class of $\mathbb Z^2$: norms from $\mathbb Z[\sqrt c]$ modulo units

**Layer:** $\mathbb Q$.

For $c\in\mathbb Z$, $c\ne0$, let $Q_c = x_0^2 - c\,x_1^2$ over $\mathcal O_\mathbb Q$ (`normForm c` $=\langle1,-c\rangle$). At the class of
$L = \mathbb Z^2$ (the double coset of $1$):
* the representations $R(L, m)$ (`repSet … 1`) are the integral vectors $x\in\mathbb Z^2$ with $Q_c(x) = m$, i.e. the
  elements $z = x_0 + x_1\sqrt c$ of $\mathbb Z[\sqrt c]$ of norm $m$ (`normSet c m`);
* the unit group $\Gamma_1 = SO(L)$ (`levelGroup … 1`) consists of the integral rotations
  $\begin{psmallmatrix}a&cb\\b&a\end{psmallmatrix}$, $a^2-cb^2 = 1$, i.e. multiplication by the norm-one units $a+b\sqrt c$.

Hence (**`tsum_orbits_repSet_one`**) the number of $\Gamma_1$-orbits on $R(L,m)$ is the number of orbits of
$\mathrm{unitary}(\mathbb Z[\sqrt c])$ on the elements of norm $m$, and if the genus has one proper class
(**`repCount_normForm`**) this is $n(M_i, m)$ for the unique class $i$.
-/
import QuadFormsKB.Tamagawa.Classical.OrbitEquiv
import QuadFormsKB.Tamagawa.Classical.BinaryOneClass
import QuadFormsKB.Tamagawa.Classical.NormCount

open NumberField IsDedekindDomain Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.HilbertModular LocalDensity

/-- **$x_0^2 - c\,x_1^2$ over $\mathcal O_\mathbb Q$**, as $\langle1, -c\rangle$ (`diagForm1`). Parameter: `c`. -/
abbrev normForm (c : ℤ) : QuadForm (𝓞 ℚ) 2 := diagForm1 (((-c : ℤ)) : 𝓞 ℚ)

local notation "QF" c => formF (normForm c)

variable (c : ℤ)

theorem dIn_normForm : dIn (((-c : ℤ)) : 𝓞 ℚ) ℚ = -(c : ℚ) := by
  simp [dIn]

theorem eval_normForm (x : Fin 2 → ℚ) : (QF c).eval x = x 0 ^ 2 - c * x 1 ^ 2 := by
  rw [eval_formF_diag]; simp; ring

theorem intCast_mem_range (k : ℤ) : (k : ℚ) ∈ (algebraMap (𝓞 ℚ) ℚ).range := ⟨k, by simp⟩

theorem exists_int_of_mem_range {q : ℚ} (h : q ∈ (algebraMap (𝓞 ℚ) ℚ).range) : ∃ k : ℤ, q = k := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) a, ?_⟩
  conv_lhs => rw [← (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm_apply_apply a]
  simp

/-! ### The representations at the class of $\mathbb Z^2$ -/

variable {c} {m : ℤ}

/-- The column of an element $z = x_0 + x_1\sqrt c$. -/
def colZ (z : ℤ√c) : Fin 2 → ℚ := ![(z.re : ℚ), (z.im : ℚ)]

theorem eval_colZ (z : ℤ√c) : (QF c).eval (colZ z) = (z.norm : ℚ) := by
  rw [eval_normForm, Zsqrtd.norm_def]; simp [colZ]; ring

theorem colZ_injective : Function.Injective (colZ (c := c)) := by
  intro z z' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [colZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_inj] at h0 h1
  exact Zsqrtd.ext h0 h1

theorem qF_colZ (z : normSet c m) :
    qF (normForm c) (colZ z.1) = algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ) := by
  show (QF c).eval (colZ z.1) = _
  rw [eval_colZ, z.2]; simp

/-- **The rational frame of an element of norm $m$.** -/
def frameZ (z : normSet c m) : RatFrame (normForm c) (DVR.unary (m : 𝓞 ℚ)) :=
  (ratFrameEquivRatSphere (n' := 1) (normForm c) (m : 𝓞 ℚ)).symm
    (⟨colZ z.1, qF_colZ z⟩ : RatSphere (normForm c) (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)))

theorem frameZ_col (z : normSet c m) (i : Fin 2) : (frameZ z).1 i 0 = colZ z.1 i := rfl

/-- **Integral finite-adelic frames are integral vectors.** -/
theorem ratFT_mem_latHatT_iff (X : RatFrame (normForm c) (DVR.unary (m : 𝓞 ℚ))) :
    ratFT (normForm c) (DVR.unary (m : 𝓞 ℚ)) X ∈ latHatT ℚ 2 1 ↔
      ∀ i, X.1 i 0 ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
  have key : ∀ (q : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)),
      (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
    intro q v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  · intro h i
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ (X.1 i 0) fun v => ?_
    have := h 0 i v
    exact (key _ v).1 this
  · intro h j i v
    rw [Subsingleton.elim j 0]
    show (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (X.1 i 0)) v ∈ _
    rw [key]
    obtain ⟨a, ha⟩ := h i
    rw [← ha]
    exact v.valuation_le_one a

theorem mem_repSet_one_iff (y : Fin 1 → VInf ℚ 2) :
    y ∈ repSet (ratAT_smul (normForm c) (DVR.unary (m : 𝓞 ℚ))) (ratFT_smul _ _) (latHatT_stable (normForm c))
        (1 : SOAf (normForm c)) ↔
      ∃ z : normSet c m, ratAT (normForm c) (DVR.unary (m : 𝓞 ℚ)) (frameZ z) = y := by
  rw [mem_repSet, one_smul]
  constructor
  · rintro ⟨X, hX, rfl⟩
    have hX' := (ratFT_mem_latHatT_iff X).1 hX
    obtain ⟨a, ha⟩ := exists_int_of_mem_range (hX' 0)
    obtain ⟨b, hb⟩ := exists_int_of_mem_range (hX' 1)
    have hcol : colZ (⟨a, b⟩ : ℤ√c) = fun i => X.1 i 0 := by
      funext i; fin_cases i
      · simp [colZ, ha]
      · simp [colZ, hb]
    have hnorm : (⟨a, b⟩ : ℤ√c).norm = m := by
      have h1 := (compMat_unary_iff (n' := 1) (normForm c) (m : 𝓞 ℚ) X.1).1 X.2
      rw [← hcol] at h1
      have h2 : (((⟨a, b⟩ : ℤ√c).norm : ℤ) : ℚ) = (m : ℚ) := by
        rw [← eval_colZ]; simpa using h1
      exact_mod_cast h2
    refine ⟨(⟨⟨a, b⟩, hnorm⟩ : normSet c m), ?_⟩
    congr 1
    apply Subtype.ext
    ext i j
    rw [Subsingleton.elim j 0]
    exact congrFun hcol i
  · rintro ⟨z, rfl⟩
    refine ⟨frameZ z, (ratFT_mem_latHatT_iff _).2 fun i => ?_, rfl⟩
    rw [frameZ_col]
    fin_cases i
    · exact intCast_mem_range _
    · exact intCast_mem_range _

/-! ### The unit group at the class of $\mathbb Z^2$ -/

variable (c)

/-- The rotation $\begin{psmallmatrix}a&cb\\b&a\end{psmallmatrix}$ of a norm-one unit $u = a + b\sqrt c$, in $SO(V)(\mathbb Q)$. -/
def unitSO (u : unitary (ℤ√c)) : soSub (QF c) ℚ :=
  have h : ((u : ℤ√c).re : ℚ) ^ 2 + dIn (((-c : ℤ)) : 𝓞 ℚ) ℚ * ((u : ℤ√c).im : ℚ) ^ 2 = 1 := by
    have hn : (u : ℤ√c).norm = 1 := (Zsqrtd.norm_eq_one_iff_mem_unitary).2 u.2
    rw [Zsqrtd.norm_def] at hn
    rw [dIn_normForm]
    have : (((u : ℤ√c).re * (u : ℤ√c).re - c * (u : ℤ√c).im * (u : ℤ√c).im : ℤ) : ℚ) = 1 := by
      rw [hn]; simp
    push_cast at this
    linear_combination this
  ⟨⟨rotGL _ h (one_pow 2), rotGL_mem _ _ _⟩, by
    show (rotMat _ _ _ 1).det = 1
    exact det_rotMat h⟩

variable {c}

theorem ratMat_unitSO (u : unitary (ℤ√c)) :
    ratMat (normForm c) (unitSO c u) = rotMat (-(c : ℚ)) ((u : ℤ√c).re : ℚ) ((u : ℤ√c).im : ℚ) 1 := by
  show rotMat (dIn _ ℚ) _ _ 1 = _
  rw [dIn_normForm]

theorem rotMat_mulVec_colZ (u z : ℤ√c) :
    rotMat (-(c : ℚ)) (u.re : ℚ) (u.im : ℚ) 1 *ᵥ colZ z = colZ (u * z) := by
  funext i
  fin_cases i <;> simp [rotMat, colZ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The element of $\Gamma$ of a norm-one unit. -/
abbrev unitΓ (u : unitary (ℤ√c)) : GammaSOAdele (normForm c) := ⟨diagSOAdele _ (unitSO c u), ⟨unitSO c u, rfl⟩⟩

theorem gammaEquiv_symm_unitΓ (u : unitary (ℤ√c)) :
    (gammaEquiv (normForm c)).symm (unitΓ u) = unitSO c u := by
  rw [MulEquiv.symm_apply_eq]
  rfl

theorem unitΓ_smul_frameZ (u : unitary (ℤ√c)) (z : normSet c m) :
    unitΓ u • frameZ z = frameZ (u • z) := by
  apply Subtype.ext
  rw [ratFrame_smul_val, gammaEquiv_symm_unitΓ, ratMat_unitSO]
  ext i j
  rw [Subsingleton.elim j 0, frameZ_col, normSet_smul_val, ← rotMat_mulVec_colZ]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, frameZ_col]

/-- **Integrality of a rational rotation**: $\gamma_f \in SO(\hat L)$ iff $\gamma$ has integral entries (for
$\gamma\in SO(V)(\mathbb Q)$, $\gamma = \begin{psmallmatrix}a&cb\\b&a\end{psmallmatrix}$). -/
theorem finHom_mem_KSO_iff (δ : soSub (QF c) ℚ) (hc : c ≠ 0) :
    finHom (normForm c) δ ∈ KSO (normForm c) ↔
      ∃ u : unitary (ℤ√c), δ = unitSO c u := by
  let _ : MulAction (OAf (QF c)) (Lat ℚ 2) := latAction (QF c)
  have hKiff : ∀ δ' : soSub (QF c) ℚ, finHom (normForm c) δ' ∈ KSO (normForm c) ↔
      glImage ((δ' : orthGroup (QF c) ℚ) : GL (Fin 2) ℚ) intVec = intVec := by
    intro δ'
    rw [KSO, Subgroup.mem_subgroupOf, ← stabilizer_eq_locStab, MulAction.mem_stabilizer_iff]
    show latSMul (QF c) (diagF (QF c) (δ' : orthGroup (QF c) ℚ)) (Tamagawa.stdLat ℚ 2) = _ ↔ _
    rw [diagF_smul]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hKiff]
  have hD : (((-c : ℤ)) : 𝓞 ℚ) ≠ 0 := by
    simpa using hc
  constructor
  · intro h
    obtain ⟨hval, -, hnorm, -⟩ := orth_diag _ hD (δ : orthGroup (QF c) ℚ).2
    have hdet : ((δ : orthGroup (QF c) ℚ) : GL (Fin 2) ℚ).val.det = 1 := mem_soSub.mp δ.2
    set g := ((δ : orthGroup (QF c) ℚ) : GL (Fin 2) ℚ) with hg
    have he0 : g.val *ᵥ ![1, 0] ∈ (intVec : Submodule (𝓞 ℚ) (Fin 2 → ℚ)) := by
      rw [← h]
      exact (mem_glImage).2 ⟨_, e0_mem_intVec, rfl⟩
    have hcol : g.val *ᵥ ![1, 0] = ![g.val 0 0, g.val 1 0] := by
      rw [hval, rotMat_mulVec_single, ← hval]
    rw [hcol] at he0
    obtain ⟨a, ha⟩ := exists_int_of_mem_range (he0 0)
    obtain ⟨b, hb⟩ := exists_int_of_mem_range (he0 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at ha hb
    have hn : (⟨a, b⟩ : ℤ√c).norm = 1 := by
      rw [Zsqrtd.norm_def]
      have h1 := hnorm
      rw [ha, hb, dIn_normForm] at h1
      have : ((a * a - c * b * b : ℤ) : ℚ) = 1 := by push_cast; linear_combination h1
      exact_mod_cast this
    refine ⟨⟨⟨a, b⟩, (Zsqrtd.norm_eq_one_iff_mem_unitary).1 hn⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    show g.val = rotMat (dIn _ ℚ) (a : ℚ) (b : ℚ) 1
    rw [hval, hdet, ← ha, ← hb]
  · rintro ⟨u, rfl⟩
    have hS : ∀ q : ℤ, (q : ℚ) ∈ (algebraMap (𝓞 ℚ) ℚ).range := intCast_mem_range
    have hd : dIn (((-c : ℤ)) : 𝓞 ℚ) ℚ ∈ (algebraMap (𝓞 ℚ) ℚ).range := range_dIn _
    exact glImage_intVec_eq (rotMat_mem hd (hS _) (hS _) (Subring.one_mem _))
      (rotMatInv_mem hd (hS _) (hS _) (Subring.one_mem _))

/-- **The unit group at the class of $\mathbb Z^2$** is the image of the norm-one units. -/
theorem mem_levelGroup_one_iff (hc : c ≠ 0) (a : GInfSO (normForm c)) :
    a ∈ levelGroup (GammaSOAdele (normForm c)) (KSO (normForm c)) 1 ↔
      ∃ u : unitary (ℤ√c), (unitΓ u : SOAdele (normForm c)).1 = a := by
  rw [mem_levelGroup_iff]
  constructor
  · rintro ⟨g, ⟨δ, rfl⟩, rfl, hK⟩
    simp only [inv_one, one_mul, mul_one] at hK
    obtain ⟨u, rfl⟩ := (finHom_mem_KSO_iff δ hc).1 hK
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨_, (unitΓ u).2, rfl, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    exact (finHom_mem_KSO_iff _ hc).2 ⟨u, rfl⟩

/-! ### The count -/

/-- **The orbits at the class of $\mathbb Z^2$ are the orbits of the norm-one units on the elements of norm $m$.** -/
theorem tsum_orbits_repSet_one (hc : c ≠ 0) (m : ℤ) :
    (∑' _ : orbitRel.Quotient (levelGroup (GammaSOAdele (normForm c)) (KSO (normForm c)) 1)
        (repSet (ratAT_smul (normForm c) (DVR.unary (m : 𝓞 ℚ))) (ratFT_smul _ _) (latHatT_stable (normForm c))
          (1 : SOAf (normForm c))), (1 : ℝ≥0∞)) =
      ∑' _ : orbitRel.Quotient (unitary (ℤ√c)) (normSet c m), (1 : ℝ≥0∞) := by
  set S := repSet (ratAT_smul (normForm c) (DVR.unary (m : 𝓞 ℚ))) (ratFT_smul _ _) (latHatT_stable (normForm c))
    (1 : SOAf (normForm c))
  have hinj : Function.Injective fun z : normSet c m => ratAT (normForm c) (DVR.unary (m : 𝓞 ℚ)) (frameZ z) := by
    intro z z' h
    have h1 := ratAT_injective _ _ h
    apply Subtype.ext
    apply colZ_injective
    funext i
    rw [← frameZ_col, ← frameZ_col, h1]
  let f : normSet c m ≃ S := Equiv.ofBijective (fun z => ⟨_, (mem_repSet_one_iff _).2 ⟨z, rfl⟩⟩)
    ⟨fun z z' h => hinj (congrArg Subtype.val h), fun y => by
      obtain ⟨z, hz⟩ := (mem_repSet_one_iff (y : Fin 1 → VInf ℚ 2)).1 y.2
      exact ⟨z, Subtype.ext hz⟩⟩
  have hf : ∀ z, (f z : Fin 1 → VInf ℚ 2) = ratAT (normForm c) (DVR.unary (m : 𝓞 ℚ)) (frameZ z) := fun _ => rfl
  have hsmul : ∀ (u : unitary (ℤ√c)) (z : normSet c m),
      (unitΓ u : SOAdele (normForm c)).1 • ratAT (normForm c) (DVR.unary (m : 𝓞 ℚ)) (frameZ z) =
        ratAT (normForm c) (DVR.unary (m : 𝓞 ℚ)) (frameZ (u • z)) := fun u z => by
    rw [← ratAT_smul, unitΓ_smul_frameZ]
  symm
  refine tsum_orbitQuot_eq f fun z z' => ?_
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨(unitΓ u : SOAdele (normForm c)).1, (mem_levelGroup_one_iff hc _).2 ⟨u, rfl⟩⟩, Subtype.ext ?_⟩
    show (unitΓ u : SOAdele (normForm c)).1 • (f z' : Fin 1 → VInf ℚ 2) = f (u • z')
    rw [hf, hf, hsmul]
  · rintro ⟨⟨a, ha⟩, h⟩
    obtain ⟨u, rfl⟩ := (mem_levelGroup_one_iff hc a).1 ha
    refine ⟨u, hinj ?_⟩
    have h' : (unitΓ u : SOAdele (normForm c)).1 • (f z' : Fin 1 → VInf ℚ 2) = f z := congrArg Subtype.val h
    rw [hf, hf, hsmul] at h'
    exact h'

/-- **$n(M_i, m)$ with one class in the genus**: if the genus of $\mathbb Z^2$ for $x_0^2 - cx_1^2$ has one proper class,
the number of representations of $m$ by the class, modulo its units, is the number of elements of norm $m$ of
$\mathbb Z[\sqrt c]$ modulo the norm-one units. -/
theorem repCount_normForm (hc : c ≠ 0) [Subsingleton (DC (normForm c))] (m : ℤ) (i : DC (normForm c)) :
    Indefinite.repCount (normForm c) (DVR.unary (m : 𝓞 ℚ)) i =
      ∑' _ : orbitRel.Quotient (unitary (ℤ√c)) (normSet c m), (1 : ℝ≥0∞) := by
  have hi : (⟦dcRep (normForm c) i⟧ : DC (normForm c)) = ⟦1⟧ := Subsingleton.elim _ _
  obtain ⟨γ, hγ, k, hk, hb⟩ := Quotient.exact hi.symm
  unfold Indefinite.repCount unitGroup repsT
  rw [hb]
  rw [tsum_orbits_repSet_eq (ratAT_smul (normForm c) (DVR.unary (m : 𝓞 ℚ))) (ratFT_smul _ _)
    (latHatT_stable (normForm c)) 1 hγ hk]
  exact tsum_orbits_repSet_one hc m

end QuadFormsKB.Tamagawa.Classical
