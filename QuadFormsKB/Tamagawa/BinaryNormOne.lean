import QuadFormsKB.Tamagawa.BinaryFrameStep

/-!
# The norm-one vectors of $x^2 + Dy^2$ and the reduction of $\tau^{\mathrm{reg}}(SO_2) = 2$ to a mass formula

**Layer:** $F$ totally real (any class number), $D \in \mathcal O_F$ with $\langle1,D\rangle = x^2 + Dy^2$ totally positive definite
(`diagForm1 D`, the representative of each square class), $V = (F^2, \langle1,D\rangle)$, $L = \mathcal O_F^2$
(the lattice of the order
$\mathcal O_F[\sqrt{-D}]$ in the coordinates $1, \sqrt{-D}$).

**The algebra.** Over any field $K \supseteq F$ with $2 \ne 0$, every $g \in O(V)(K)$ is determined by its first column $(a, b)$ and its
determinant $s = \pm1$: $g = \begin{pmatrix}a & -Dbs\\ b & as\end{pmatrix}$ with $a^2 + Db^2 = 1$ (`orth_eq_rotMat`). (These are
multiplication by $a + b\sqrt{-D}$, composed with conjugation when $s = -1$.)

**Consequences.**
* `eq_glImage_rotGL_of_mem`: a lattice $M$ in the genus of $L$ that contains a vector $x$ with $Q(x) = 1$ is $\gamma_xL$, $\gamma_x$ the
  rotation with first column $x$. *Proof:* locally $M_\mathfrak p = g_\mathfrak pL_\mathfrak p$; $h = \gamma_x^{-1}g_\mathfrak p$ has
  $e_0 \in hL_\mathfrak p$, so the first column of $h^{-1}$ is integral, hence all of $h^{\pm1}$ is, and $hL_\mathfrak p = L_\mathfrak p$.
* `card_autLat_std`: $|O(L)| = 2\,r_L(1)$ ($\gamma \mapsto (\gamma e_0, \det\gamma)$).
* **`repMass_diagForm1_one`**: $\mathrm{repMass}(L, 1) = \sum_{\mathrm{cls}M\subseteq\mathrm{gen}L} r_M(1)/|O(M)| = \tfrac12$ (only the class
  of $L$ represents $1$). No class number, no local density.
* **`tauSOReg_diagForm1_eq_two_iff`**: with the regularized step $1\to2$ at $a = 1$ (`two_mul_tamagawaKReg_mul_repMass`),
  $$\tau^{\mathrm{reg}}(SO\langle1,D\rangle) = 2 \iff \mathrm{Mass}(L)\cdot S^{\mathrm{reg}}_2(\langle1,D\rangle, 1) = 1 ,$$
  i.e. $\tau^{\mathrm{reg}}(SO_2) = 2$ is **the mass formula of the order $\mathcal O_F[\sqrt{-D}]$** with Siegel's local factors at the
  number $1$. `binaryTamagawaTwoRegDiag_iff_massFormula` states this for all $D$ at once.

Source: Weil 1982, §4.5, p. 100 (the fibration over the sphere $Q(x) = \rho$) [unverified locator]; Shimura 2010, §4 (orders of
CM fields and norm forms) [unverified].
-/

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryNormOne

open Lattices LocalDensity QuadForm QuadFormsKB.HilbertModular

/-! ### The orthogonal group of $\langle 1, D\rangle$ over a commutative ring -/

section Algebra

variable {R : Type*} [CommRing R]

/-- The isometry with first column $(a, b)$ and determinant $s$: $\begin{pmatrix}a & -Dbs\\ b & as\end{pmatrix}$. -/
def rotMat (D a b s : R) : Matrix (Fin 2) (Fin 2) R := !![a, -D * b * s; b, a * s]

/-- Its inverse (for $a^2 + Db^2 = 1$, $s^2 = 1$): $\begin{pmatrix}a & Db\\ -bs & as\end{pmatrix}$. -/
def rotMatInv (D a b s : R) : Matrix (Fin 2) (Fin 2) R := !![a, D * b; -b * s, a * s]

/-- The Hessian $\mathrm{diag}(2, 2D)$ of $\langle1,D\rangle$. -/
def hessD (D : R) : Matrix (Fin 2) (Fin 2) R := !![2, 0; 0, 2 * D]

theorem rotMat_mul_rotMatInv {D a b s : R} (h : a ^ 2 + D * b ^ 2 = 1) (hs : s ^ 2 = 1) :
    rotMat D a b s * rotMatInv D a b s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h + D * b ^ 2 * hs
  · linear_combination (-(a * D * b)) * hs
  · linear_combination (-(a * b)) * hs
  · linear_combination h + a ^ 2 * hs

theorem rotMatInv_mul_rotMat {D a b s : R} (h : a ^ 2 + D * b ^ 2 = 1) (hs : s ^ 2 = 1) :
    rotMatInv D a b s * rotMat D a b s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, rotMatInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf
  · linear_combination h
  · linear_combination s ^ 2 * h + hs

theorem rotMat_isometry {D a b s : R} (h : a ^ 2 + D * b ^ 2 = 1) (hs : s ^ 2 = 1) :
    (rotMat D a b s)ᵀ * hessD D * rotMat D a b s = hessD D := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, hessD, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  · linear_combination 2 * h
  · linear_combination 2 * D * s ^ 2 * h + 2 * D * hs

theorem det_rotMat {D a b s : R} (h : a ^ 2 + D * b ^ 2 = 1) : (rotMat D a b s).det = s := by
  rw [Matrix.det_fin_two]; simp [rotMat]; linear_combination s * h

theorem rotMat_mulVec_single (D a b s : R) : rotMat D a b s *ᵥ ![1, 0] = ![a, b] := by
  ext i; fin_cases i <;> simp [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rotMatInv_mulVec_self {D a b : R} (h : a ^ 2 + D * b ^ 2 = 1) : rotMatInv D a b 1 *ᵥ ![a, b] = ![1, 0] := by
  ext i; fin_cases i <;> simp [rotMatInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · linear_combination h
  · ring

/-- **Every isometry of $\langle1,D\rangle$ is a rotation or a rotation composed with conjugation** (over a field with $2 \ne 0$,
$D \ne 0$): $g = \begin{pmatrix}a & -Dbs\\ b & as\end{pmatrix}$, $a = g_{00}$, $b = g_{10}$, $s = \det g$, with $a^2 + Db^2 = 1$ and
$s^2 = 1$. *Proof:* the entries of $g^{\mathsf T}Hg = H$ give $a^2+Db^2 = 1$, $ac + Dbe = 0$, $c^2 + De^2 = D$ for $g = (a\ c; b\ e)$;
then $c = c(a^2+Db^2) = -Db(ae - cb)$ and $e = a(ae - cb)$. -/
theorem orth_eq_rotMat {K : Type*} [Field K] {d : K} (h2 : (2 : K) ≠ 0) (hd : d ≠ 0) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : gᵀ * hessD d * g = hessD d) :
    g = rotMat d (g 0 0) (g 1 0) g.det ∧ g 0 0 ^ 2 + d * g 1 0 ^ 2 = 1 ∧ g.det ^ 2 = 1 := by
  have e00 := congrFun (congrFun hg 0) 0
  have e01 := congrFun (congrFun hg 0) 1
  have e11 := congrFun (congrFun hg 1) 1
  simp [hessD, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  rw [Matrix.det_fin_two]
  have h1 : g 0 0 ^ 2 + d * g 1 0 ^ 2 = 1 := by
    apply mul_left_cancel₀ h2; linear_combination e00
  have h01 : g 0 0 * g 0 1 + d * g 1 0 * g 1 1 = 0 := by
    apply mul_left_cancel₀ h2; linear_combination e01
  have h11 : g 0 1 ^ 2 + d * g 1 1 ^ 2 = d := by
    apply mul_left_cancel₀ h2; linear_combination e11
  have hc : g 0 1 = -d * g 1 0 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
    linear_combination (-g 0 1) * h1 + g 0 0 * h01
  have he : g 1 1 = g 0 0 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
    linear_combination (-g 1 1) * h1 + g 1 0 * h01
  refine ⟨?_, h1, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]
    · linear_combination hc
    · exact he
  · apply mul_left_cancel₀ hd
    generalize g 0 0 * g 1 1 - g 0 1 * g 1 0 = s at hc he ⊢
    rw [hc, he] at h11
    linear_combination h11 - d * s ^ 2 * h1

end Algebra

/-! ### $\langle1,D\rangle$ over a number field -/

section NF

variable {F : Type} [Field F] [NumberField F]

/-- $D$ in an $F$-algebra $K$. -/
abbrev dIn (D : 𝓞 F) (K : Type*) [CommRing K] [Algebra F K] : K := algebraMap F K (algebraMap (𝓞 F) F D)

theorem hessian_map_formF_diag (D : 𝓞 F) (K : Type*) [CommRing K] [Algebra F K] :
    (formF (diagForm1 D)).hessian.map (algebraMap F K) = hessD (dIn D K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hessD, dIn, formF, QuadForm.map, QuadForm.hessian, diagForm1, QuadForm.diag, Matrix.diagonal] <;> ring

theorem evalIn_formF_diag (D : 𝓞 F) (K : Type*) [CommRing K] [Algebra F K] (x : Fin 2 → K) :
    (formF (diagForm1 D)).evalIn K x = x 0 ^ 2 + dIn D K * x 1 ^ 2 := by
  simp [QuadForm.evalIn, dIn, formF, QuadForm.map, diagForm1, QuadForm.diag, Matrix.diagonal, Fin.sum_univ_two]
  ring

theorem eval_formF_diag (D : 𝓞 F) (x : Fin 2 → F) :
    (formF (diagForm1 D)).eval x = x 0 ^ 2 + algebraMap (𝓞 F) F D * x 1 ^ 2 := by
  rw [QuadForm.eval, evalIn_formF_diag]; rfl

theorem mem_orthGroup_diag_iff (D : 𝓞 F) {K : Type*} [CommRing K] [Algebra F K] {g : GL (Fin 2) K} :
    g ∈ orthGroup (formF (diagForm1 D)) K ↔ g.valᵀ * hessD (dIn D K) * g.val = hessD (dIn D K) := by
  rw [mem_orthGroup, hessian_map_formF_diag]

/-- The rotation (or rotation-conjugation) with first column $(a,b)$ and determinant $s$, as an element of $\mathrm{GL}_2(K)$. -/
def rotGL (D : 𝓞 F) {K : Type*} [CommRing K] [Algebra F K] {a b s : K} (h : a ^ 2 + dIn D K * b ^ 2 = 1)
    (hs : s ^ 2 = 1) : GL (Fin 2) K :=
  ⟨rotMat (dIn D K) a b s, rotMatInv (dIn D K) a b s, rotMat_mul_rotMatInv h hs, rotMatInv_mul_rotMat h hs⟩

theorem rotGL_mem (D : 𝓞 F) {K : Type*} [CommRing K] [Algebra F K] {a b s : K} (h : a ^ 2 + dIn D K * b ^ 2 = 1)
    (hs : s ^ 2 = 1) : rotGL D h hs ∈ orthGroup (formF (diagForm1 D)) K :=
  (mem_orthGroup_diag_iff D).mpr (rotMat_isometry h hs)

/-- **The isometries of $\langle1,D\rangle$ over a field $K \supseteq F$:** $g = \begin{pmatrix}a & -Dbs\\ b & as\end{pmatrix}$, $g^{-1} =
\begin{pmatrix}a & Db\\ -bs & as\end{pmatrix}$ with $a^2+Db^2 = 1$, $s = \det g = \pm1$. -/
theorem orth_diag (D : 𝓞 F) (hD : D ≠ 0) {K : Type*} [Field K] [Algebra F K] [CharZero K]
    {g : GL (Fin 2) K} (hg : g ∈ orthGroup (formF (diagForm1 D)) K) :
    g.val = rotMat (dIn D K) (g.val 0 0) (g.val 1 0) g.val.det ∧
      g⁻¹.val = rotMatInv (dIn D K) (g.val 0 0) (g.val 1 0) g.val.det ∧
      g.val 0 0 ^ 2 + dIn D K * g.val 1 0 ^ 2 = 1 ∧ g.val.det ^ 2 = 1 := by
  have hd : dIn D K ≠ 0 := by
    simp only [dIn]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hD)
  obtain ⟨h1, h2, h3⟩ := orth_eq_rotMat (two_ne_zero) hd ((mem_orthGroup_diag_iff D).mp hg)
  refine ⟨h1, ?_, h2, h3⟩
  have e := rotMat_mul_rotMatInv (D := dIn D K) h2 h3
  rw [← h1] at e
  calc g⁻¹.val = g⁻¹.val * (g.val * rotMatInv (dIn D K) (g.val 0 0) (g.val 1 0) g.val.det) := by rw [e, mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-! ### Lattices in the genus of $\mathcal O_F^2$ that represent $1$ -/

section Local

variable (D : 𝓞 F) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem valued_dIn_le_one : Valued.v (dIn D Fv) ≤ 1 := by
  have := valued_int_le_one v D
  rwa [IsScalarTower.algebraMap_apply (𝓞 F) F Fv] at this

theorem valued_sign_eq_one {s : Fv} (hs : s ^ 2 = 1) : Valued.v s = 1 := by
  have hs' : s * s = 1 := by rw [← sq]; exact hs
  rcases mul_self_eq_one_iff.mp hs' with h | h <;> simp [h]

theorem valued_rotMat_le_one {a b s : Fv} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hs : Valued.v s ≤ 1) :
    ∀ i j, Valued.v (rotMat (dIn D Fv) a b s i j) ≤ 1 := by
  have hd := valued_dIn_le_one D v
  intro i j; fin_cases i <;> fin_cases j <;> simp [rotMat, map_mul, Valuation.map_neg] <;>
    first | assumption | exact mul_le_one' (mul_le_one' hd hb) hs | exact mul_le_one' ha hs

theorem valued_rotMatInv_le_one {a b s : Fv} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hs : Valued.v s ≤ 1) :
    ∀ i j, Valued.v (rotMatInv (dIn D Fv) a b s i j) ≤ 1 := by
  have hd := valued_dIn_le_one D v
  intro i j; fin_cases i <;> fin_cases j <;> simp [rotMatInv, map_mul, Valuation.map_neg] <;>
    first | assumption | exact mul_le_one' hd hb | exact mul_le_one' hb hs | exact mul_le_one' ha hs

/-- **A local isometry whose inverse carries $e_0$ into $\mathfrak o_\mathfrak p^2$ stabilizes $\mathfrak o_\mathfrak p^2$:** the first column
$(a, -bs)$ of $h^{-1}$ is integral, so all entries of $h$ and $h^{-1}$ are (`orth_diag`). -/
theorem locAct_std_of_inv_mem (hD : D ≠ 0) {h : GL (Fin 2) Fv} (hh : h ∈ orthGroup (formF (diagForm1 D)) Fv)
    (hy : h⁻¹.val *ᵥ ![1, 0] ∈ std v) : locAct v h (std v) = std v := by
  obtain ⟨e1, e2, -, e4⟩ := orth_diag D hD hh
  have hcol : h⁻¹.val *ᵥ ![1, 0] = ![h.val 0 0, -(h.val 1 0) * h.val.det] := by
    rw [e2]; ext i; fin_cases i <;> simp [rotMatInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hcol] at hy
  have hs := valued_sign_eq_one v e4
  have ha : Valued.v (h.val 0 0) ≤ 1 := by simpa using hy 0
  have hb : Valued.v (h.val 1 0) ≤ 1 := by
    have := hy 1
    simpa [map_mul, Valuation.map_neg, hs] using this
  have hent : ∀ i j, Valued.v (h.val i j) ≤ 1 := by
    rw [e1]; exact valued_rotMat_le_one D v ha hb hs.le
  have hent' : ∀ i j, Valued.v (h⁻¹.val i j) ≤ 1 := by
    rw [e2]; exact valued_rotMatInv_le_one D v ha hb hs.le
  ext y
  rw [mem_locAct]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mulVec_mem_std v hent hz
  · intro hy'
    exact ⟨h⁻¹.val *ᵥ y, mulVec_mem_std v hent' hy', mulVec_inv_mulVec h y⟩

end Local

section Global

variable (D : 𝓞 F)

theorem vec_eq_cons (x : Fin 2 → F) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> rfl

theorem norm_one_of_eval {x : Fin 2 → F} (hQx : (formF (diagForm1 D)).eval x = 1) :
    x 0 ^ 2 + dIn D F * x 1 ^ 2 = 1 := by
  rw [eval_formF_diag] at hQx; simpa [dIn] using hQx

/-- The rotation $\gamma_x$ with first column $x$, for $Q(x) = 1$. -/
abbrev rotOf {x : Fin 2 → F} (hQx : (formF (diagForm1 D)).eval x = 1) : GL (Fin 2) F :=
  rotGL D (norm_one_of_eval D hQx) (one_pow 2)

theorem rotOf_mulVec {x : Fin 2 → F} (hQx : (formF (diagForm1 D)).eval x = 1) :
    (rotOf D hQx).val *ᵥ ![1, 0] = x := by
  show rotMat _ (x 0) (x 1) 1 *ᵥ _ = x
  rw [rotMat_mulVec_single]; exact (vec_eq_cons x).symm

/-- **A lattice in the genus of $\mathcal O_F^2$ containing a vector of norm $1$ is isometric to $\mathcal O_F^2$:** if
$x \in M$, $Q(x) = 1$, then $M = \gamma_x\,\mathcal O_F^2$ ($\gamma_x$ the rotation with first column $x$). *Proof:* by localizations
(`loc_injective`): $M_\mathfrak p = g\,\mathfrak o_\mathfrak p^2$ and $h = \gamma_x^{-1}g$ satisfies $h^{-1}e_0 = g^{-1}x \in \mathfrak o_\mathfrak p^2$,
so $h\,\mathfrak o_\mathfrak p^2 = \mathfrak o_\mathfrak p^2$ (`locAct_std_of_inv_mem`). -/
theorem eq_glImage_rotOf_of_mem (hD : D ≠ 0) {M : Lat F 2}
    (hM : SameGenus (formF (diagForm1 D)) intVec M.1) {x : Fin 2 → F} (hx : x ∈ M.1)
    (hQx : (formF (diagForm1 D)).eval x = 1) :
    glImage (rotOf D hQx) intVec = M.1 := by
  set Q := formF (diagForm1 D)
  set γ := rotOf D hQx
  have hγ : γ ∈ orthGroup Q F := rotGL_mem D _ _
  refine loc_injective (glImage_isLattice γ intVec_isLattice) M.2 fun v => ?_
  rw [loc_glImage, loc_intVec]
  obtain ⟨g, hg, hgM⟩ := hM v
  rw [loc_intVec] at hgM
  rw [← hgM]
  set γv := Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ
  have hγv : γv ∈ orthGroup Q (v.adicCompletion F) := (orthMap Q (v.adicCompletion F) ⟨γ, hγ⟩).2
  set h := γv⁻¹ * g
  have hh : h ∈ orthGroup Q (v.adicCompletion F) := (orthGroup Q _).mul_mem ((orthGroup Q _).inv_mem hγv) hg
  have hxv : locVec v x ∈ locAct v g (std v) := hgM ▸ locVec_mem_loc v hx
  obtain ⟨z, hz, hzx⟩ := (mem_locAct).mp hxv
  have hy : h⁻¹.val *ᵥ ![1, 0] ∈ std v := by
    have e : h⁻¹.val *ᵥ ![1, 0] = z := by
      have h1 : γv.val *ᵥ ![1, 0] = locVec v x := by
        rw [← rotOf_mulVec D hQx, locVec_mulVec]
        congr 1
        ext i; fin_cases i <;> simp
      rw [show h⁻¹ = g⁻¹ * γv by simp [h], Units.val_mul, ← mulVec_mulVec, h1, ← hzx, mulVec_mulVec,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [e]; exact hz
  have hstab := locAct_std_of_inv_mem D v hD hh hy
  rw [show g = γv * h by simp [h], locAct_mul, hstab]

/-- An integral matrix with integral inverse stabilizes $\mathcal O_F^n$. -/
theorem glImage_intVec_eq {n : ℕ} {γ : GL (Fin n) F} (h1 : ∀ i j, γ.val i j ∈ (algebraMap (𝓞 F) F).range)
    (h2 : ∀ i j, γ⁻¹.val i j ∈ (algebraMap (𝓞 F) F).range) : glImage γ intVec = intVec := by
  have key : ∀ {A : Matrix (Fin n) (Fin n) F}, (∀ i j, A i j ∈ (algebraMap (𝓞 F) F).range) →
      ∀ {y : Fin n → F}, y ∈ (intVec : Submodule (𝓞 F) (Fin n → F)) → A *ᵥ y ∈ (intVec : Submodule (𝓞 F) (Fin n → F)) := by
    intro A hA y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hy j)
  ext y
  rw [mem_glImage]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact key h1 hz
  · intro hy; exact ⟨γ⁻¹.val *ᵥ y, key h2 hy, mulVec_inv_mulVec γ y⟩

theorem rotMat_mem {S : Subring F} {d a b s : F} (hd : d ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hs : s ∈ S) :
    ∀ i j, rotMat d a b s i j ∈ S := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [rotMat] <;>
    first | assumption | exact S.mul_mem (S.mul_mem hd hb) hs | exact S.mul_mem ha hs

theorem rotMatInv_mem {S : Subring F} {d a b s : F} (hd : d ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hs : s ∈ S) :
    ∀ i j, rotMatInv d a b s i j ∈ S := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [rotMatInv] <;>
    first | assumption | exact S.mul_mem hd hb | exact S.mul_mem hb hs | exact S.mul_mem ha hs

/-- $\pm1$ indexed by a boolean. -/
def signOf (b : Bool) : F := if b then 1 else -1

theorem signOf_sq (b : Bool) : (signOf b : F) ^ 2 = 1 := by cases b <;> simp [signOf]

theorem e0_mem_intVec : (![1, 0] : Fin 2 → F) ∈ (intVec : Submodule (𝓞 F) (Fin 2 → F)) := by
  intro i; fin_cases i
  · exact ⟨1, map_one _⟩
  · exact ⟨0, map_zero _⟩

theorem eval_e0 : (formF (diagForm1 D)).eval ![1, 0] = 1 := by
  rw [eval_formF_diag]; simp

theorem range_dIn : dIn D F ∈ (algebraMap (𝓞 F) F).range := ⟨D, rfl⟩

theorem range_signOf (b : Bool) : (signOf b : F) ∈ (algebraMap (𝓞 F) F).range := by
  cases b
  · exact ⟨-1, by simp [signOf]⟩
  · exact ⟨1, by simp [signOf]⟩

/-- **$|O(\mathcal O_F^2)| = 2\,r_{\mathcal O_F^2}(1)$**: $\gamma \mapsto (\gamma e_0, \det\gamma)$ is a bijection from $O(\mathcal O_F^2)$ onto
$\{x \in \mathcal O_F^2 : Q(x) = 1\}\times\{\pm1\}$ (`orth_diag`; the inverse is $(x, s) \mapsto$ `rotGL`). -/
theorem card_autLat_std (hD : D ≠ 0) :
    Nat.card (autLat (formF (diagForm1 D)) intVec) =
      repCount (formF (diagForm1 D)) (Tamagawa.stdLat F 2) 1 * 2 := by
  classical
  set Q := formF (diagForm1 D)
  let A := {x : Fin 2 → F // x ∈ (Tamagawa.stdLat F 2).1 ∧ Q.eval x = 1}
  have hR : ∀ (x : A) (b : Bool), glImage (rotGL D (norm_one_of_eval D x.2.2) (signOf_sq b)) intVec = intVec :=
    fun x b => glImage_intVec_eq
      (rotMat_mem (range_dIn D) (x.2.1 0) (x.2.1 1) (range_signOf b))
      (rotMatInv_mem (range_dIn D) (x.2.1 0) (x.2.1 1) (range_signOf b))
  let fwd : autLat Q intVec → A × Bool := fun γ =>
    (⟨γ.1.1.val *ᵥ ![1, 0], by
        refine ⟨?_, ?_⟩
        · have hγ : glImage γ.1.1 intVec = intVec := (mem_autLat Q).mp γ.2
          show γ.1.1.val *ᵥ ![1, 0] ∈ (intVec : Submodule (𝓞 F) (Fin 2 → F))
          have := mulVec_mem_glImage (γ := γ.1.1) (e0_mem_intVec (F := F))
          rwa [hγ] at this
        · rw [eval_mulVec_of_mem Q γ.1.2]; exact eval_e0 D⟩,
      decide (γ.1.1.val.det = 1))
  let bwd : A × Bool → autLat Q intVec := fun p =>
    ⟨⟨rotGL D (norm_one_of_eval D p.1.2.2) (signOf_sq p.2), rotGL_mem D _ _⟩, (mem_autLat Q).mpr (hR p.1 p.2)⟩
  have e : autLat Q intVec ≃ A × Bool :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun γ => by
        obtain ⟨e1, -, e3, e4⟩ := orth_diag D hD γ.1.2
        refine Subtype.ext (Subtype.ext (Units.ext ?_))
        show rotMat (dIn D F) ((γ.1.1.val *ᵥ ![1, 0]) 0) ((γ.1.1.val *ᵥ ![1, 0]) 1)
          (signOf (decide (γ.1.1.val.det = 1))) = γ.1.1.val
        have hs : signOf (decide (γ.1.1.val.det = 1)) = γ.1.1.val.det := by
          have h' : γ.1.1.val.det * γ.1.1.val.det = 1 := by rw [← sq]; exact e4
          rcases mul_self_eq_one_iff.mp h' with h | h
          · simp [signOf, h]
          · rw [h]; simp [signOf]; norm_num
        rw [hs]
        conv_rhs => rw [e1]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      right_inv := fun p => by
        obtain ⟨x, b⟩ := p
        refine Prod.ext (Subtype.ext ?_) ?_
        · show rotMat (dIn D F) (x.1 0) (x.1 1) (signOf b) *ᵥ ![1, 0] = x.1
          rw [rotMat_mulVec_single]; exact (vec_eq_cons x.1).symm
        · show decide ((rotMat (dIn D F) (x.1 0) (x.1 1) (signOf b)).det = 1) = b
          rw [det_rotMat (norm_one_of_eval D x.2.2)]
          cases b
          · simp [signOf]; norm_num
          · simp [signOf] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  rfl

variable [IsTotallyReal F]

/-- **$\mathrm{repMass}(\mathcal O_F^2, 1) = \tfrac12$ for $\langle1,D\rangle$:** in
$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}(\mathcal O_F^2)}r_M(1)/|O(M)|$ only the class of $\mathcal O_F^2$ contributes
(`eq_glImage_rotOf_of_mem`), and $r_{\mathcal O_F^2}(1)/|O(\mathcal O_F^2)| = \tfrac12$ (`card_autLat_std`). No class number and no local
density enter. -/
@[kb "weil1982" "§4.5, p. 100 (the sphere Q(x) = ρ is one O(V)(F)-orbit; n = 2, ρ = 1) [unverified locator]"]
theorem repMass_diagForm1_one (hpd : IsTotallyPosDef (formF (diagForm1 D))) :
    repMass (formF (diagForm1 D)) (Tamagawa.stdLat F 2) 1 = 1 / 2 := by
  classical
  set Q := formF (diagForm1 D)
  have hD : D ≠ 0 := by
    have h := nondegenerate_of_isTotallyPosDef hpd
    rw [QuadForm.Nondegenerate, hessian_det_diagForm1] at h
    exact right_ne_zero_of_mul h
  have hint : IsIntegral Q (Tamagawa.stdLat F 2).1 := HilbertModular.isIntegral_stdLat (diagForm1 D)
  have hfin := genusClasses_finite hpd (Tamagawa.stdLat F 2) hint
  have hmem : Quotient.mk (latSetoid Q) (Tamagawa.stdLat F 2) ∈ hfin.toFinset :=
    (Set.Finite.mem_toFinset _).mpr ⟨Tamagawa.stdLat F 2, rfl, SameGenus.refl Q _⟩
  rw [repMass, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_eq_single_of_mem _ hmem]
  · show (repCount Q (Tamagawa.stdLat F 2) 1 : ℝ) / (Nat.card (autLat Q intVec) : ℕ) = 1 / 2
    rw [card_autLat_std D hD]
    have hne : repCount Q (Tamagawa.stdLat F 2) 1 ≠ 0 := by
      have := finite_repSet hpd (Tamagawa.stdLat F 2).2 hint 1
      have hne : Nonempty {v : Fin 2 → F // v ∈ (Tamagawa.stdLat F 2).1 ∧ Q.eval v = 1} :=
        ⟨⟨![1, 0], e0_mem_intVec, eval_e0 D⟩⟩
      exact Nat.card_ne_zero.mpr ⟨hne, this⟩
    have : (repCount Q (Tamagawa.stdLat F 2) 1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne
    push_cast
    rw [← div_div, div_self this]
  · intro c hc hne
    obtain ⟨M, rfl, hM⟩ := (Set.Finite.mem_toFinset _).mp hc
    have h0 : repCount Q M 1 = 0 := by
      by_contra h
      obtain ⟨⟨x, hx, hQx⟩⟩ := (Nat.card_ne_zero.mp h).1
      apply hne
      apply Quotient.sound
      exact IsIsometric.symm Q ⟨rotOf D hQx, rotGL_mem D _ _, eq_glImage_rotOf_of_mem D hD hM hx hQx⟩
    show (repCount Q M 1 : ℝ) / _ = 0
    rw [h0, Nat.cast_zero, zero_div]

/-- **$\tau^{\mathrm{reg}}(SO_2) = 2$ for $\langle1,D\rangle$ is the mass formula of $\mathcal O_F^2$ with Siegel's factors at $1$:**
$$\tau^{\mathrm{reg}}(SO\langle1,D\rangle) = 2 \iff \mathrm{Mass}(\mathcal O_F^2)\cdot S^{\mathrm{reg}}_2(\langle1,D\rangle, 1) = 1,$$
$S^{\mathrm{reg}}_2(\langle1,D\rangle,1) = |d_F|^{-1/2}\prod_\sigma\beta_\sigma(1)\cdot L_F(1,\chi)^{-1}\prod_\mathfrak p\beta_\mathfrak p(\langle1,D\rangle,1)
(1-\chi(\mathfrak p)/N\mathfrak p)^{-1}$ (`siegelProduct2Reg`). *Proof:* the step $1\to2$ at $a = 1$
(`two_mul_tamagawaKReg_mul_repMass`) with $\mathrm{repMass}(\mathcal O_F^2, 1) = \tfrac12$ (`repMass_diagForm1_one`) gives
$\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO}) = S^{\mathrm{reg}}_2(\langle1,D\rangle,1)$, and $\tau^{\mathrm{reg}} = 2\mu^{\mathrm{reg}}\,\mathrm{Mass}$. -/
@[kb "weil1982" "§4.5, p. 100 and p. 109 (Siegel's theorem from the fibration over the sphere, one number, N = 2) [unverified]"]
theorem tauSOReg_diagForm1_eq_two_iff (hpd : IsTotallyPosDef (formF (diagForm1 D))) :
    tauSOReg (diagForm1 D) = 2 ↔
      mass (formF (diagForm1 D)) (Tamagawa.stdLat F 2) * siegelProduct2Reg (diagForm1 D) 1 = 1 := by
  have h1pos : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F 1) := fun v => by simp
  have hrep : ∃ ξ, (formF (diagForm1 D)).eval ξ = algebraMap (𝓞 F) F 1 :=
    ⟨![1, 0], by rw [eval_e0, map_one]⟩
  have key := two_mul_tamagawaKReg_mul_repMass (diagForm1 D) hpd h1pos hrep
  rw [map_one, repMass_diagForm1_one D hpd] at key
  have hQ := nondegenerate_of_isTotallyPosDef hpd
  rw [tauSOReg_eq _ hQ hpd]
  constructor
  · intro h
    linear_combination (-mass (formF (diagForm1 D)) (Tamagawa.stdLat F 2)) * key + (1 / 2 : ℝ) * h
  · intro h
    linear_combination 2 * h + 2 * mass (formF (diagForm1 D)) (Tamagawa.stdLat F 2) * key

/-- **`BinaryTamagawaTwoRegDiag F` is the mass formula for the orders $\mathcal O_F[\sqrt{-D}]$** (every totally real $F$, any class
number): $\tau^{\mathrm{reg}}(SO_2) = 2$ for all totally definite binary forms iff, for every $D$ with $\langle1,D\rangle$ totally
positive definite, $\mathrm{Mass}(\mathcal O_F^2, \langle1,D\rangle)\cdot S^{\mathrm{reg}}_2(\langle1,D\rangle, 1) = 1$. -/
theorem binaryTamagawaTwoRegDiag_iff_massFormula :
    BinaryTamagawaTwoRegDiag F ↔ ∀ D : 𝓞 F, IsTotallyPosDef (formF (diagForm1 D)) →
      mass (formF (diagForm1 D)) (Tamagawa.stdLat F 2) * siegelProduct2Reg (diagForm1 D) 1 = 1 :=
  ⟨fun h D hpd => (tauSOReg_diagForm1_eq_two_iff D hpd).mp (h.tau_eq_two D hpd),
    fun h => ⟨fun D hpd => (tauSOReg_diagForm1_eq_two_iff D hpd).mpr (h D hpd)⟩⟩

end Global

end NF

end QuadFormsKB.Tamagawa.BinaryNormOne
