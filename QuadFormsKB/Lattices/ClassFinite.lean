/-
# Finiteness of the class number of every genus over a number field (O'Meara 103:3–103:4)

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$, $Q$ = `Q : QuadForm F n` nondegenerate (definite or
indefinite), as in `Lattices/{Genus,ClassSet,Finite}.lean`. The bilinear form is $B(x, y) = x^{\mathsf T}Hy$ (`bil`), so
$B(x, x) = 2Q(x)$.

**Defines** `IsDualBounded Q M c` ($c\,M^\# \subseteq M$, where $M^\# = \{x : B(x, M) \subseteq \mathcal O_F\}$; the
"bounded volume" condition, satisfied uniformly on a genus by `exists_dual_zsmul_mem`) and `gramOf Q x` (the Gram matrix
$(B(x_i, x_j))_{ij}$ of a family of vectors).

**Proves**
* `exists_free_sublattice`: every lattice $M$ contains a free lattice $P\mathcal O_F^n$ with $k M \subseteq P\mathcal O_F^n$ for a
  positive integer $k \le K_F$ (Steinitz `exists_gl_free_part` + `exists_scale_ideal`).
* `exists_value_set` (O'Meara 103:3): a finite set $\Theta \subseteq F^\times$ such that every integral lattice with
  $c M^\# \subseteq M$ has a vector $x$ with $Q(x) \in \Theta$.
* `exists_gram_basis` (the induction of 103:4): a finite set $S$ of $n \times n$ matrices such that every such $M$ contains
  an $F$-basis $x_0, \dots, x_{n-1}$ of $V$ with Gram matrix in $S$.
* **`classes_finite`** (O'Meara 103:4): integral lattices with $c M^\# \subseteq M$ fall into finitely many classes.
* **`genusClasses_finite_of_nondegenerate`**: the genus of an integral lattice contains finitely many classes, for every
  nondegenerate $Q$; **`genusClasses_finite_nf`**: The same for every lattice (no integrality); the totally definite
  `genusClasses_finite` is recovered as `genusClasses_finite_of_totallyPosDef`.
* **`exists_genus_reps`** (the form used by O'Meara 104:1): finitely many lattices $L_1, \dots, L_h$ in $\mathrm{gen}(L)$
  such that every lattice in $\mathrm{gen}(L)$ is isometric to one of them.

*Proof (O'Meara 103:3–103:4, adapted).*
1. *Free sublattice.* $M \cong \mathcal O_F^{n-1} \oplus \mathfrak c$ (Steinitz); scaling $\mathfrak c$ into a small integral ideal
   gives $P$ with $P\mathcal O_F^n \subseteq M$, $kM \subseteq P\mathcal O_F^n$, $k \le K_F$. Then
   $G = P^{\mathsf T}HP$ has $ck^2G^{-1}$ integral, so $|N(\det G)| \le |ck^2|^{n[F:\mathbb Q]}$ and $|N(\det P)|$ is bounded.
2. *103:3, anisotropic $V$:* 103:2 (`exists_short`) gives $0 \ne x \in P\mathcal O_F^n$ with all conjugates of all
   coordinates bounded, so $Q(x) \ne 0$ is an algebraic integer with bounded conjugates: finitely many values.
   *Isotropic $V$* (O'Meara uses maximal lattices and hyperbolic planes here; this is a shorter route): take an isotropic
   $v$, scale its coordinate ideal to a small integral ideal ($x = bv = P\xi$ with $m_1 \in (\xi_i)$, $m_1 \le C_F$), and put
   $y = P\,\mathrm{adj}(G)\,r$ where $\sum_i r_i\xi_i = m_1$; then $B(x, y) = \beta = m_1\det G$ has bounded norm $m_\beta$,
   and $Q(y + tx) = Q(y) + t\beta$ can be reduced modulo $m_\beta$ to a nonzero value with bounded conjugates.
3. *103:4, induction on $n$:* move $x$ with $Q(x) = \alpha \in \Theta$ to a fixed $y_\alpha$ by an isometry (two symmetries,
   in place of Witt's theorem), and apply the induction hypothesis to $M \cap y_\alpha^\perp$ in coordinates for
   $y_\alpha^\perp$ (its dual bound is $2\alpha c$, since $2\alpha m - B(m, y)y \in M \cap y^\perp$).
4. *Rigidity:* if $x$ is a basis in $M$ with Gram matrix $G$ then $\mathcal O_F^n \subseteq X^{-1}M \subseteq \delta_G^{-1}\mathcal O_F^n$,
   finitely many lattices; equal $(G, X^{-1}M)$ give isometric lattices ($X'X^{-1} \in O(V)$).

O'Meara, *Introduction to Quadratic Forms* (1973), §103 (printed pp. 305–310 = PDF pp. 313–318).
-/
import QuadFormsKB.Lattices.ClassFiniteAux
import QuadFormsKB.Lattices.Steinitz
import QuadFormsKB.Lattices.CartanDieudonne
import QuadFormsKB.Lattices.FreeBridge

open NumberField Module Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices.ClassFin

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### The dual bound and Gram matrices -/

section Defs

variable (Q : QuadForm F n)

/-- **Bounded dual** $c\,M^\# \subseteq M$: every $x \in F^n$ with $B(x, M) \subseteq \mathcal O_F$ has $c\,x \in M$ ($c \in \mathbb Z$).
On a genus this holds with one $c$ for all members (`exists_dual_zsmul_mem`); it plays the role of O'Meara's condition
$\mathfrak v L \supseteq \mathfrak c$ on the volume in 103:3–103:4. -/
@[kb "omeara1963" "§103, 103:3–103:4, pp. 307–310 (volume condition 𝔳L ⊇ 𝔠)"]
def IsDualBounded (M : Submodule (𝓞 F) (Fin n → F)) (c : ℤ) : Prop :=
  ∀ x : Fin n → F, (∀ m ∈ M, bil Q x m ∈ (algebraMap (𝓞 F) F).range) → c • x ∈ M

/-- **The Gram matrix** $(B(x_i, x_j))_{ij}$ of vectors $x_0, \dots, x_{k-1} \in F^n$. -/
def gramOf {k : ℕ} (x : Fin k → Fin n → F) : Matrix (Fin k) (Fin k) F :=
  Matrix.of fun i j => bil Q (x i) (x j)

theorem hessian_map_id : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp

theorem eval_add (a b : Fin n → F) : Q.eval (a + b) = Q.eval a + Q.eval b + bil Q a b := by
  have h := QuadForm.polar_eq_hessian F Q a b
  rw [hessian_map_id] at h
  rw [bil, ← h]; ring

theorem eval_smul (t : F) (a : Fin n → F) : Q.eval (t • a) = t ^ 2 * Q.eval a := evalIn_smul' Q t a

theorem bil_add_left (a b c : Fin n → F) : bil Q (a + b) c = bil Q a c + bil Q b c := by
  simp [bil, add_dotProduct]

theorem bil_sub_left (a b c : Fin n → F) : bil Q (a - b) c = bil Q a c - bil Q b c := by
  simp [bil, sub_dotProduct]

theorem bil_add_right (a b c : Fin n → F) : bil Q c (a + b) = bil Q c a + bil Q c b := by
  simp [bil, mulVec_add, dotProduct_add]

theorem bil_sub_right (a b c : Fin n → F) : bil Q c (a - b) = bil Q c a - bil Q c b := by
  simp [bil, mulVec_sub, dotProduct_sub]

theorem bil_sum_left {k : ℕ} (a : Fin k → F) (x : Fin k → Fin n → F) (y : Fin n → F) :
    bil Q (∑ i, a i • x i) y = ∑ i, a i * bil Q (x i) y := by
  simp [bil, sum_dotProduct, smul_dotProduct]

/-- $B(e_i, w) = (Hw)_i$. -/
theorem bil_single (i : Fin n) (w : Fin n → F) : bil Q (Pi.single i 1) w = (Q.hessian *ᵥ w) i := by
  simp [bil, single_dotProduct]

/-- $B(P\xi, P\eta) = \xi^{\mathsf T}(P^{\mathsf T}HP)\eta$. -/
theorem bil_mulVec (P : Matrix (Fin n) (Fin n) F) (ξ η : Fin n → F) :
    bil Q (P *ᵥ ξ) (P *ᵥ η) = ξ ⬝ᵥ ((Pᵀ * Q.hessian * P) *ᵥ η) := by
  rw [bil, dotProduct_comm (P *ᵥ ξ), dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
    mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem gramOf_eq (x : Fin n → Fin n → F) :
    gramOf Q x = (Matrix.of fun r i => x i r)ᵀ * Q.hessian * (Matrix.of fun r i => x i r) := by
  ext i j
  have : x i = (Matrix.of fun r i => x i r) *ᵥ Pi.single i 1 := by
    funext r; simp
  have h2 : x j = (Matrix.of fun r i => x i r) *ᵥ Pi.single j 1 := by
    funext r; simp
  rw [gramOf, of_apply, this, h2, bil_mulVec]
  simp [single_dotProduct]

/-- Isometries preserve integrality and the dual bound. -/
theorem isIntegral_glImage {M : Submodule (𝓞 F) (Fin n → F)} (hM : Lattices.IsIntegral Q M)
    {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) : Lattices.IsIntegral Q (glImage γ M) := by
  rintro _ ⟨m, hm, rfl⟩
  have := evalIn_mulVec_of_mem Q hγ m
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  rw [this]; exact hM m hm

theorem isDualBounded_glImage {M : Submodule (𝓞 F) (Fin n → F)} {c : ℤ} (hM : IsDualBounded Q M c)
    {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) : IsDualBounded Q (glImage γ M) c := by
  intro x hx
  have hγ' : γ⁻¹ ∈ orthGroup Q F := (orthGroup Q F).inv_mem hγ
  have h1 : ∀ m ∈ M, bil Q (γ⁻¹.val *ᵥ x) m ∈ (algebraMap (𝓞 F) F).range := by
    intro m hm
    have := hx _ (mulVec_mem_glImage (γ := γ) hm)
    rwa [← bil_isometry Q hγ', mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec] at this
  have h2 := hM _ h1
  refine ⟨_, h2, ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  rw [mulVec_smul, mulVec_inv_mulVec]

/-- **Moving a vector by an isometry** (in place of Witt's theorem, O'Meara 42:17): if $Q(x) = Q(y) \ne 0$ then
$\gamma x = y$ for some $\gamma \in O(V)$, a product of at most two symmetries. -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem), special case; cassels1978 Ch. 2, Lemma 4.2, Cor. 1, p. 20"]
theorem exists_orth_mulVec_eq {x y : Fin n → F} (hxy : Q.eval x = Q.eval y) (hx : Q.eval x ≠ 0) :
    ∃ γ ∈ orthGroup Q F, γ.val *ᵥ x = y := by
  have hyx : Q.evalIn F y = Q.evalIn F x := hxy.symm
  by_cases h1 : Q.evalIn F (y - x) ≠ 0
  · exact ⟨_, (symm Q F (y - x)).2, symm_sub_apply Q F hyx h1⟩
  · have h4 := evalIn_sub_add_evalIn_add Q F hyx
    have hy : Q.evalIn F y ≠ 0 := hyx ▸ hx
    have h2 : Q.evalIn F (y + x) ≠ 0 := by
      intro h0; rw [not_not.mp h1, h0, add_zero] at h4
      exact hy (by linear_combination -h4 / 4)
    refine ⟨(symm Q F y : GL (Fin n) F) * (symm Q F (y + x) : GL (Fin n) F),
      (orthGroup Q F).mul_mem (symm Q F y).2 (symm Q F (y + x)).2, ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, symm_add_apply Q F hyx h2, symm_neg_self Q F hy]

end Defs

/-! ### A free sublattice of bounded index -/

/-- **A free sublattice of bounded index:** there is $K_F \in \mathbb N$ such that every lattice $M \subseteq F^n$ has
$P \in \mathrm{GL}_n(F)$ with $P\mathcal O_F^n \subseteq M$ and $k\,P^{-1}M \subseteq \mathcal O_F^n$ for some integer
$0 < k \le K_F$. (Steinitz: $M = \gamma(\mathcal O_F^{n-1} \oplus \mathfrak c)$; replace $\mathfrak c$ by $a_0\mathcal O_F$ with
$a_0 \in \mathfrak c$, $b a_0 = m_0$, $b\mathfrak c \subseteq \mathcal O_F$, `exists_scale_ideal`.) -/
@[kb "omeara1963" "§103, proof of 103:3, step 3, p. 308 (with 81:5, p. 212)"]
theorem exists_free_sublattice :
    ∃ K : ℕ, ∀ M : Submodule (𝓞 F) (Fin n → F), M.IsLattice F →
      ∃ P : GL (Fin n) F, (∀ ξ ∈ intVec, P.val *ᵥ ξ ∈ M) ∧
        ∃ k : ℕ, 0 < k ∧ k ≤ K ∧ ∀ x ∈ M, (k : F) • (P⁻¹.val *ᵥ x) ∈ intVec := by
  classical
  cases n with
  | zero =>
    refine ⟨1, fun M _ => ⟨1, fun ξ _ => ?_, 1, one_pos, le_rfl, fun x _ i => i.elim0⟩⟩
    rw [Subsingleton.elim ((1 : GL (Fin 0) F).val *ᵥ ξ) 0]; exact M.zero_mem
  | succ m =>
    obtain ⟨C, hC⟩ := exists_scale_ideal (F := F)
    refine ⟨C, fun M hM => ?_⟩
    obtain ⟨γ, hγ₁, hγ₂⟩ := Steinitz.exists_gl_free_part hM
    set 𝔠 : Submodule (𝓞 F) F := (glImage γ⁻¹ M).map
      ((LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).restrictScalars (𝓞 F)) with h𝔠
    have hmem𝔠 : ∀ x ∈ M, (γ⁻¹.val *ᵥ x) (Fin.last m) ∈ 𝔠 := fun x hx =>
      ⟨_, mulVec_mem_glImage hx, rfl⟩
    have h𝔠fg : 𝔠.FG := ((hM.fg.map _).map _)
    have h𝔠0 : 𝔠 ≠ ⊥ := by
      intro h0
      have hz : ∀ x ∈ M, (γ⁻¹.val *ᵥ x) (Fin.last m) = 0 := fun x hx => by
        have := hmem𝔠 x hx; rw [h0] at this; exact (Submodule.mem_bot _).mp this
      let φ : (Fin (m + 1) → F) →ₗ[F] F :=
        (LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).comp (Matrix.mulVecLin γ⁻¹.val)
      have hle : Submodule.span F (M : Set (Fin (m + 1) → F)) ≤ LinearMap.ker φ :=
        Submodule.span_le.mpr fun x hx => by simpa [φ] using hz x hx
      rw [hM.span_eq_top] at hle
      have h1 := hle (Submodule.mem_top (x := γ.val *ᵥ Pi.single (Fin.last m) 1))
      simp only [LinearMap.mem_ker, φ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
        LinearMap.coe_proj, Function.eval, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mulVec, Pi.single_eq_same] at h1
      exact one_ne_zero h1
    obtain ⟨b, hb0, hbint, a₀, ha₀, m₀, hm₀, hm₀C, hba⟩ := hC 𝔠 h𝔠fg h𝔠0
    obtain ⟨z₀, ⟨x₀, hx₀, rfl⟩, hz₀⟩ := ha₀
    have ha0 : a₀ ≠ 0 := by
      rintro rfl; rw [mul_zero] at hba; exact hm₀.ne' (by exact_mod_cast hba.symm)
    -- the diagonal correction `D = diag(1, …, 1, a₀)`
    set d : Fin (m + 1) → F := fun i => if i = Fin.last m then a₀ else 1 with hd
    have hd0 : ∀ i, d i ≠ 0 := fun i => by simp only [hd]; split_ifs <;> simp [ha0]
    let D : GL (Fin (m + 1)) F := ⟨diagonal d, diagonal fun i => (d i)⁻¹,
      by rw [diagonal_mul_diagonal]; simp [mul_inv_cancel₀ (hd0 _)],
      by rw [diagonal_mul_diagonal]; simp [inv_mul_cancel₀ (hd0 _)]⟩
    have hx₀dec : x₀ = ∑ i : Fin m, (γ⁻¹.val *ᵥ x₀) i.castSucc • (γ.val *ᵥ Pi.single i.castSucc 1) +
        a₀ • (γ.val *ᵥ Pi.single (Fin.last m) 1) := by
      have e : x₀ = γ.val *ᵥ (γ⁻¹.val *ᵥ x₀) := (mulVec_inv_mulVec γ x₀).symm
      conv_lhs => rw [e]
      conv_lhs => rw [← Finset.univ_sum_single (γ⁻¹.val *ᵥ x₀)]
      rw [Fin.sum_univ_castSucc, mulVec_add, mulVec_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
      · have hz₀' : (γ⁻¹.val *ᵥ x₀) (Fin.last m) = a₀ := hz₀
        rw [← mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one, hz₀']
    have hlastM : a₀ • (γ.val *ᵥ Pi.single (Fin.last m) 1) ∈ M := by
      have : a₀ • (γ.val *ᵥ Pi.single (Fin.last m) 1) = x₀ - ∑ i : Fin m,
          (γ⁻¹.val *ᵥ x₀) i.castSucc • (γ.val *ᵥ Pi.single i.castSucc 1) := by
        rw [eq_sub_iff_add_eq]; exact (add_comm _ _).trans hx₀dec.symm
      rw [this]
      exact M.sub_mem hx₀ (M.sum_mem fun i _ => Steinitz.intSmul_mem (hγ₂ x₀ hx₀ i) (hγ₁ i))
    refine ⟨γ * D, fun ξ hξ => ?_, m₀, hm₀, hm₀C, fun x hx => ?_⟩
    · -- columns of `γ D` lie in `M`
      obtain ⟨c, rfl⟩ := eq_sum_of_mem_intVec hξ
      rw [mulVec_sum]
      refine M.sum_mem fun i _ => ?_
      rw [mulVec_smul]
      refine M.smul_mem _ ?_
      rw [Units.val_mul, ← mulVec_mulVec]
      have hD : D.val *ᵥ (Pi.single i 1 : Fin (m + 1) → F) = d i • Pi.single i 1 := by
        change diagonal d *ᵥ _ = _
        rw [mulVec_single, ← Pi.single_smul', smul_eq_mul, mul_one]
        funext j; simp [Pi.single_apply]
      rw [hD, mulVec_smul]
      induction i using Fin.lastCases with
      | last => simpa [hd] using hlastM
      | cast i =>
        have : d i.castSucc = 1 := by simp [hd, (Fin.castSucc_lt_last i).ne]
        rw [this, one_smul]; exact hγ₁ i
    · -- `m₀ (γ D)⁻¹ x` is integral
      intro i
      have hinv : ((γ * D)⁻¹).val *ᵥ x = diagonal (fun i => (d i)⁻¹) *ᵥ (γ⁻¹.val *ᵥ x) := by
        rw [_root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec]; rfl
      rw [Pi.smul_apply, hinv, mulVec_diagonal, smul_eq_mul]
      induction i using Fin.lastCases with
      | last =>
        have hba' : (m₀ : F) * a₀⁻¹ = b := by
          rw [← hba, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
        simp only [hd, ↓reduceIte]
        rw [← mul_assoc, hba']
        exact hbint _ (hmem𝔠 x hx)
      | cast i =>
        simp only [hd, (Fin.castSucc_lt_last i).ne, ↓reduceIte, inv_one, one_mul]
        obtain ⟨a, ha⟩ := hγ₂ x hx i
        exact ⟨m₀ * a, by rw [map_mul, ha, map_natCast]⟩

/-! ### Bounded Gram determinants of free sublattices -/

section Common

variable {Q : QuadForm F n}

theorem gram_entry_mem {M : Submodule (𝓞 F) (Fin n → F)} (hMi : Lattices.IsIntegral Q M)
    {P : Matrix (Fin n) (Fin n) F} (hP : ∀ ξ ∈ intVec, P *ᵥ ξ ∈ M) (i j : Fin n) :
    (Pᵀ * Q.hessian * P) i j ∈ (algebraMap (𝓞 F) F).range := by
  have := bil_mem Q hMi (hP _ (single_one_mem_intVec i)) (hP _ (single_one_mem_intVec j))
  rw [bil_mulVec] at this
  simpa [mulVec_single_one, single_dotProduct] using this

theorem gram_symm (P : Matrix (Fin n) (Fin n) F) : (Pᵀ * Q.hessian * P)ᵀ = Pᵀ * Q.hessian * P := by
  rw [transpose_mul, transpose_mul, transpose_transpose, QuadForm.hessian_transpose, Matrix.mul_assoc]

/-- **The dual bound in coordinates:** if $P\mathcal O_F^n \subseteq M$, $k\,P^{-1}M \subseteq \mathcal O_F^n$ and
$c\,M^\# \subseteq M$, then $ck^2\,G^{-1}$ is integral for $G = P^{\mathsf T}HP$. -/
theorem dual_int {M : Submodule (𝓞 F) (Fin n → F)} {c : ℤ} (hMd : IsDualBounded Q M c)
    {P : GL (Fin n) F} (hP : ∀ ξ ∈ intVec, P.val *ᵥ ξ ∈ M) {k : ℕ}
    (hk : ∀ x ∈ M, (k : F) • (P⁻¹.val *ᵥ x) ∈ intVec)
    (hG : (P.valᵀ * Q.hessian * P.val).det ≠ 0) (i j : Fin n) :
    ((c * k ^ 2 : ℤ) : F) * (P.valᵀ * Q.hessian * P.val)⁻¹ i j ∈ (algebraMap (𝓞 F) F).range := by
  set G := P.valᵀ * Q.hessian * P.val with hGdef
  set v : Fin n → F := G⁻¹ *ᵥ Pi.single j 1
  set z : Fin n → F := P.val *ᵥ v
  have hGG : G * G⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)
  have hdual : ∀ m ∈ M, bil Q ((k : F) • z) m ∈ (algebraMap (𝓞 F) F).range := by
    intro m hm
    set u := P⁻¹.val *ᵥ m
    have hm' : m = P.val *ᵥ u := (mulVec_inv_mulVec P m).symm
    have e : bil Q ((k : F) • z) m = ((k : F) • u) j := by
      rw [bil_smul_left, hm', bil_mulVec, Pi.smul_apply, smul_eq_mul]
      congr 1
      rw [dotProduct_mulVec, ← mulVec_transpose, gram_symm, mulVec_mulVec, hGG, one_mulVec,
        single_dotProduct, one_mul]
    rw [e]; exact hk m hm j
  have h1 := hMd _ hdual
  have h2 := hk _ h1
  have e : (k : F) • (P⁻¹.val *ᵥ (c • ((k : F) • z))) = ((c * k ^ 2 : ℤ) : F) • v := by
    rw [← Int.cast_smul_eq_zsmul F, mulVec_smul, mulVec_smul, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mulVec, smul_smul, smul_smul]
    congr 1; push_cast; ring
  rw [e] at h2
  have := h2 i
  simpa [v, mulVec_single_one] using this

/-- **Free sublattices with bounded Gram determinant:** for nondegenerate $Q$ and $c \ne 0$ there is $K$ such that every
integral lattice $M$ with $c\,M^\# \subseteq M$ contains $P\mathcal O_F^n$ whose Gram matrix $G = P^{\mathsf T}HP$ is integral
with $|N(\det G)| \le (|c|K^2)^{n[F:\mathbb Q]}$. -/
theorem exists_free_bounded (hQ : Q.Nondegenerate) {c : ℤ} (hc : c ≠ 0) :
    ∃ K : ℕ, ∀ M : Submodule (𝓞 F) (Fin n → F), M.IsLattice F → Lattices.IsIntegral Q M →
      IsDualBounded Q M c → ∃ P : GL (Fin n) F, (∀ ξ ∈ intVec, P.val *ᵥ ξ ∈ M) ∧
        ∃ GO : Matrix (Fin n) (Fin n) (𝓞 F), GO.map ιO = P.valᵀ * Q.hessian * P.val ∧ GO.det ≠ 0 ∧
          (Algebra.norm ℤ GO.det).natAbs ≤ (c.natAbs * K ^ 2) ^ (n * Fintype.card (OIdx F)) := by
  classical
  obtain ⟨K, hK⟩ := exists_free_sublattice (F := F) (n := n)
  refine ⟨K, fun M hM hMi hMd => ?_⟩
  obtain ⟨P, hP, k, hk0, hkK, hk⟩ := hK M hM
  refine ⟨P, hP, ?_⟩
  set G := P.valᵀ * Q.hessian * P.val with hGdef
  choose GO hGO using gram_entry_mem hMi hP
  have hGOmap : (Matrix.of GO).map ιO = G := by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, hGO]
  have hG : G.det ≠ 0 := by
    rw [hGdef, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero (isUnit_iff_ne_zero.mp (P.isUnit.map Matrix.detMonoidHom)) hQ)
      (isUnit_iff_ne_zero.mp (P.isUnit.map Matrix.detMonoidHom))
  have hdetGO : ιO (Matrix.of GO).det = G.det := by rw [RingHom.map_det, RingHom.mapMatrix_apply, hGOmap]
  have hGO0 : (Matrix.of GO).det ≠ 0 := by
    intro h; rw [h, map_zero] at hdetGO; exact hG hdetGO.symm
  refine ⟨Matrix.of GO, hGOmap, hGO0, ?_⟩
  -- `c k² G⁻¹` is integral
  choose A hA using dual_int hMd hP hk hG
  set g : ℤ := c * k ^ 2
  have hAmap : (Matrix.of A).map ιO = (g : F) • G⁻¹ := by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, hA, Matrix.smul_apply, smul_eq_mul]
  have hprod : (Matrix.of GO).det * (Matrix.of A).det = ((g ^ n : ℤ) : 𝓞 F) := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, hdetGO, RingHom.map_det, RingHom.mapMatrix_apply, hAmap, det_smul, det_nonsing_inv,
      Fintype.card_fin, Ring.inverse_eq_inv']
    rw [mul_left_comm, mul_inv_cancel₀ hG, mul_one]; simp
  have hA0 : (Matrix.of A).det ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod
    have : ((g ^ n : ℤ) : 𝓞 F) ≠ 0 := by
      have hg : g ≠ 0 := mul_ne_zero hc (pow_ne_zero _ (by exact_mod_cast hk0.ne'))
      exact_mod_cast pow_ne_zero n hg
    exact this hprod.symm
  have hnorm := congrArg (Algebra.norm ℤ) hprod
  rw [map_mul, show ((g ^ n : ℤ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (g ^ n) by simp, Algebra.norm_algebraMap,
    Module.finrank_eq_card_chooseBasisIndex] at hnorm
  have hnorm' := congrArg Int.natAbs hnorm
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at hnorm'
  have hApos : 1 ≤ (Algebra.norm ℤ (Matrix.of A).det).natAbs :=
    Int.natAbs_pos.mpr ((Algebra.norm_ne_zero_iff).mpr hA0)
  have hle : (Algebra.norm ℤ (Matrix.of GO).det).natAbs ≤ (g.natAbs ^ n) ^ Fintype.card (OIdx F) := by
    rw [← hnorm']; exact Nat.le_mul_of_pos_right _ hApos
  refine hle.trans ?_
  rw [← pow_mul]
  refine Nat.pow_le_pow_left ?_ _
  simp only [g, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkK 2)

end Common

/-! ### O'Meara 103:3: a vector with $Q(x)$ in a fixed finite set -/

section Value

variable (Q : QuadForm F n)

/-- $\sum_\varphi\sum_{i,j}|\varphi(c_{ij})|$ over the coefficients $c_{ij}$ of $Q$ and the embeddings $\varphi$. -/
def coeffW : ℝ := ∑ φ : F →+* ℂ, ∑ i, ∑ j, ‖φ (Q.coeff i j)‖

theorem norm_eval_le (φ : F →+* ℂ) {R : ℝ} (hR : 0 ≤ R) (x : Fin n → F) (hx : ∀ i, ‖φ (x i)‖ ≤ R) :
    ‖φ (Q.eval x)‖ ≤ coeffW Q * R ^ 2 := by
  have h1 : ‖φ (Q.eval x)‖ ≤ ∑ i, ∑ j, ‖φ (Q.coeff i j)‖ * R ^ 2 := by
    rw [QuadForm.eval, QuadForm.evalIn, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    split_ifs
    · rw [map_mul, map_mul, norm_mul, norm_mul, Algebra.algebraMap_self, RingHom.id_apply, sq, ← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)) (hx j) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) hR)
    · rw [map_zero, norm_zero]; positivity
  refine h1.trans ?_
  have e : ∑ i, ∑ j, ‖φ (Q.coeff i j)‖ * R ^ 2 = (∑ i, ∑ j, ‖φ (Q.coeff i j)‖) * R ^ 2 := by
    simp_rw [Finset.sum_mul]
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Finset.single_le_sum (f := fun φ : F →+* ℂ => ∑ i, ∑ j, ‖φ (Q.coeff i j)‖)
    (fun _ _ => by positivity) (Finset.mem_univ φ)

/-- $Q(y + tx) = Q(y) + t\,B(x, y)$ for an isotropic $x$. -/
theorem eval_add_smul_of_isotropic {x : Fin n → F} (hx : Q.eval x = 0) (y : Fin n → F) (t : F) :
    Q.eval (y + t • x) = Q.eval y + t * bil Q x y := by
  rw [eval_add, eval_smul, hx, bil_smul_right, bil_comm]; ring

/-- **O'Meara 103:3, bounded form:** for nondegenerate $Q$ on $F^n$ ($n \ge 1$) and $c \ne 0$ there is $B$ such that every
integral lattice $M$ with $c\,M^\# \subseteq M$ has $x \in M$ with $Q(x) \ne 0$ and $|\varphi(Q(x))| \le B$ for every
embedding $\varphi$. -/
@[kb "omeara1963" "§103, 103:3, p. 307 (bounded form)"]
theorem exists_value_bound (hn : 0 < n) {Q : QuadForm F n} (hQ : Q.Nondegenerate) {c : ℤ} (hc : c ≠ 0) :
    ∃ B : ℝ, ∀ M : Submodule (𝓞 F) (Fin n → F), M.IsLattice F → Lattices.IsIntegral Q M →
      IsDualBounded Q M c → ∃ x ∈ M, Q.eval x ≠ 0 ∧ ∀ φ : F →+* ℂ, ‖φ (Q.eval x)‖ ≤ B := by
  classical
  obtain ⟨K, hK⟩ := exists_free_bounded hQ hc
  set d := Fintype.card (OIdx F)
  set Bdet : ℕ := (c.natAbs * K ^ 2) ^ (n * d)
  by_cases hiso : ∃ v : Fin n → F, v ≠ 0 ∧ Q.eval v = 0
  · -- isotropic case
    obtain ⟨v, hv0, hv⟩ := hiso
    obtain ⟨C, hC⟩ := exists_scale_ideal (F := F)
    set Mβ : ℕ := Bdet * C ^ d
    refine ⟨Mβ * embW F + Mβ, fun M hM hMi hMd => ?_⟩
    obtain ⟨P, hP, GO, hGO, hGO0, hnorm⟩ := hK M hM hMi hMd
    set ξ₀ := P⁻¹.val *ᵥ v
    have hPξ₀ : P.val *ᵥ ξ₀ = v := mulVec_inv_mulVec P v
    set A : Submodule (𝓞 F) F := Submodule.span (𝓞 F) (Set.range ξ₀)
    have hAfg : A.FG := Submodule.fg_span (Set.finite_range ξ₀)
    have hA0 : A ≠ ⊥ := by
      have : ξ₀ ≠ 0 := by rintro h; rw [h, mulVec_zero] at hPξ₀; exact hv0 hPξ₀.symm
      obtain ⟨i, hi⟩ := Function.ne_iff.mp this
      exact (Submodule.ne_bot_iff _).mpr ⟨ξ₀ i, Submodule.subset_span ⟨i, rfl⟩, hi⟩
    obtain ⟨b, hb0, hbint, a, ha, m₁, hm₁, hm₁C, hba⟩ := hC A hAfg hA0
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp ha
    choose ξ hξ using fun i => hbint (ξ₀ i) (Submodule.subset_span ⟨i, rfl⟩)
    set x := P.val *ᵥ fun i => ιO (ξ i)
    have hxv : x = b • v := by
      have : (fun i => ιO (ξ i)) = b • ξ₀ := by funext i; simp [hξ]
      rw [show x = P.val *ᵥ fun i => ιO (ξ i) from rfl, this, mulVec_smul, hPξ₀]
    have hint : ∀ η : Fin n → 𝓞 F, (fun i => ιO (η i)) ∈ intVec := fun η i => ⟨η i, rfl⟩
    have hxM : x ∈ M := hP _ (hint ξ)
    have hx0 : Q.eval x = 0 := by rw [hxv, eval_smul, hv, mul_zero]
    set η := GO.adjugate *ᵥ r
    set y := P.val *ᵥ fun i => ιO (η i)
    have hyM : y ∈ M := hP _ (hint η)
    set e : 𝓞 F := GO.det * (m₁ : 𝓞 F)
    have hβ : bil Q x y = ιO e := by
      rw [bil_mulVec, ← hGO]
      have h1 : ((fun i => ιO (ξ i)) ⬝ᵥ (GO.map ιO *ᵥ fun i => ιO (η i))) = ιO (ξ ⬝ᵥ (GO *ᵥ η)) := by
        rw [RingHom.map_dotProduct]; congr 1; funext i; exact (RingHom.map_mulVec ιO GO η i).symm
      rw [h1, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      simp only [e]
      congr 1
      apply IsFractionRing.injective (𝓞 F) F
      rw [map_natCast, ← hba, ← hr, dotProduct, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hξ, Algebra.smul_def]; ring
    have he0 : e ≠ 0 := mul_ne_zero hGO0 (by exact_mod_cast hm₁.ne')
    set mβ := (Algebra.norm ℤ e).natAbs
    have hmβ0 : 0 < mβ := Int.natAbs_pos.mpr ((Algebra.norm_ne_zero_iff).mpr he0)
    have hmβle : mβ ≤ Mβ := by
      simp only [mβ, e, map_mul, Int.natAbs_mul]
      rw [show ((m₁ : 𝓞 F)) = algebraMap ℤ (𝓞 F) (m₁ : ℤ) by simp, Algebra.norm_algebraMap,
        Module.finrank_eq_card_chooseBasisIndex, Int.natAbs_pow, Int.natAbs_natCast]
      exact Nat.mul_le_mul hnorm (Nat.pow_le_pow_left hm₁C _)
    have hmβmem : ((mβ : ℕ) : 𝓞 F) ∈ Ideal.span {e} := by
      have := Ideal.absNorm_mem (Ideal.span {e})
      rwa [Ideal.absNorm_span_singleton] at this
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmβmem
    obtain ⟨Qy, hQy⟩ := hMi y hyM
    obtain ⟨w, q, hq, hQyd⟩ := exists_sub_mem_box mβ hmβ0 Qy
    set y₁ := y + ιO (-(w * s)) • x
    have hy₁M : y₁ ∈ M := M.add_mem hyM (by rw [algebraMap_smul]; exact M.smul_mem _ hxM)
    have hQy₁ : Q.eval y₁ = ιO (∑ k, q k • ω k) := by
      rw [eval_add_smul_of_isotropic Q hx0, hβ, show Q.eval y = ιO Qy from hQy.symm, ← map_mul, ← map_add,
        hQyd, ← hs]
      congr 1; ring
    have hqbd : ∀ φ : F →+* ℂ, ‖φ (ιO (∑ k, q k • ω k))‖ ≤ mβ * embW F := fun φ =>
      norm_sum_omega_le φ q mβ fun k => by
        have h1 := (hq k).1; have h2 := (hq k).2
        rw [abs_of_nonneg (by exact_mod_cast h1)]; exact_mod_cast h2.le
    have hW := embW_nonneg (F := F)
    have hβ₁ : bil Q x y₁ = ιO e := by
      rw [bil_add_right, bil_smul_right, bil_self, hx0, hβ]; ring
    by_cases hr0 : (∑ k, q k • ω k : 𝓞 F) = 0
    · -- use `y₁ + s x`, with value `mβ`
      refine ⟨y₁ + ιO s • x, M.add_mem hy₁M (by rw [algebraMap_smul]; exact M.smul_mem _ hxM), ?_, ?_⟩
      · rw [eval_add_smul_of_isotropic Q hx0, hQy₁, hr0, map_zero, zero_add, hβ₁, ← map_mul, hs]
        simp only [map_natCast]; exact_mod_cast hmβ0.ne'
      · intro φ
        rw [eval_add_smul_of_isotropic Q hx0, hQy₁, hr0, map_zero, zero_add, hβ₁, ← map_mul, hs, map_natCast,
          map_natCast, Complex.norm_natCast]
        have : (mβ : ℝ) ≤ Mβ := by exact_mod_cast hmβle
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) Mβ) hW]
    · refine ⟨y₁, hy₁M, ?_, fun φ => ?_⟩
      · rw [hQy₁]; intro h
        exact hr0 (IsFractionRing.injective (𝓞 F) F (by rw [h, map_zero]))
      · rw [hQy₁]
        refine (hqbd φ).trans ?_
        have : (mβ : ℝ) ≤ Mβ := by exact_mod_cast hmβle
        nlinarith [mul_le_mul_of_nonneg_right this hW, Nat.cast_nonneg (α := ℝ) Mβ]
  · -- anisotropic case
    push Not at hiso
    have hQa : ∀ v, Q.eval v = 0 → v = 0 := fun v hv => by
      by_contra h; exact hiso v h hv
    set NH : ℝ := |(Algebra.norm ℚ Q.hessian.det : ℝ)|
    have hNH : 0 < NH := by
      simp only [NH]
      exact abs_pos.mpr (by exact_mod_cast (Algebra.norm_ne_zero_iff).mpr hQ)
    set Dm : ℝ := max 1 ((Bdet : ℝ) / NH)
    set R : ℝ := ((⌊Dm⌋₊ : ℝ) + 1) * embW F
    have hR : 0 ≤ R := mul_nonneg (by positivity) embW_nonneg
    refine ⟨coeffW Q * R ^ 2, fun M hM hMi hMd => ?_⟩
    obtain ⟨P, hP, GO, hGO, hGO0, hnorm⟩ := hK M hM hMi hMd
    have hdetP : P.val.det ≠ 0 := isUnit_iff_ne_zero.mp (P.isUnit.map Matrix.detMonoidHom)
    have hdG : ιO GO.det = P.val.det ^ 2 * Q.hessian.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hGO, det_mul, det_mul, det_transpose]; ring
    have hNP : |(Algebra.norm ℚ P.val.det : ℝ)| ≤ Dm := by
      have h1 : (((Algebra.norm ℤ GO.det : ℤ) : ℚ) : ℝ) =
          (Algebra.norm ℚ P.val.det : ℝ) ^ 2 * (Algebra.norm ℚ Q.hessian.det : ℝ) := by
        rw [Algebra.coe_norm_int, show ((GO.det : 𝓞 F) : F) = ιO GO.det from rfl, hdG, map_mul, map_pow]
        push_cast; ring
      have h2 : |(((Algebra.norm ℤ GO.det : ℤ) : ℚ) : ℝ)| ≤ Bdet := by
        rw [Rat.cast_intCast, ← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hnorm
      rw [h1, abs_mul, abs_pow] at h2
      have h3 : |(Algebra.norm ℚ P.val.det : ℝ)| ^ 2 ≤ Bdet / NH := by
        rw [le_div_iff₀ hNH]; exact h2
      set y := |(Algebra.norm ℚ P.val.det : ℝ)|
      by_cases hy : y ≤ 1
      · exact hy.trans (le_max_left _ _)
      · push Not at hy
        refine le_trans ?_ (le_max_right _ _)
        nlinarith
    obtain ⟨ξ, hξ0, hξ⟩ := exists_short hn P.val hdetP Dm hNP
    set x := P.val *ᵥ fun j => ιO (ξ j)
    refine ⟨x, hP _ fun i => ⟨ξ i, rfl⟩, fun h => ?_, fun φ => norm_eval_le Q φ hR x fun i => hξ i φ⟩
    have hx0 := hQa x h
    have : (fun j => ιO (ξ j)) = 0 :=
      mulVec_injective_of_det_ne_zero P.val hdetP (by simp only [mulVec_zero]; exact hx0)
    apply hξ0
    funext j
    exact IsFractionRing.injective (𝓞 F) F (by rw [congrFun this j, Pi.zero_apply, Pi.zero_apply, map_zero])

/-- **O'Meara 103:3** (in the form needed for 103:4): for nondegenerate $Q$ on $F^n$, $n \ge 1$, and $c \ne 0$ there is a
finite set $\Theta \subseteq F \setminus \{0\}$ such that every integral lattice $M$ with $c\,M^\# \subseteq M$ has a vector
$x \in M$ with $Q(x) \in \Theta$ *Update (simplification):* in the isotropic case O'Meara passes to
$\mathfrak o$-maximal lattices and splits off hyperbolic planes (82:11, 82:20, 82:21); here an isotropic vector with almost
primitive coordinates and a partner $y$ with $B(x, y)$ of bounded norm suffice (`exists_value_bound`). -/
@[kb "omeara1963" "§103, 103:3, p. 307"]
theorem exists_value_set (hn : 0 < n) {Q : QuadForm F n} (hQ : Q.Nondegenerate) {c : ℤ} (hc : c ≠ 0) :
    ∃ Θ : Set F, Θ.Finite ∧ (0 : F) ∉ Θ ∧ ∀ M : Submodule (𝓞 F) (Fin n → F), M.IsLattice F →
      Lattices.IsIntegral Q M → IsDualBounded Q M c → ∃ x ∈ M, Q.eval x ∈ Θ := by
  obtain ⟨B, hB⟩ := exists_value_bound hn hQ hc
  refine ⟨{z | z ≠ 0 ∧ z ∈ (algebraMap (𝓞 F) F).range ∧ ∀ φ : F →+* ℂ, ‖φ z‖ ≤ B},
    (finite_bounded B).subset fun z hz => hz.2, fun h => h.1 rfl, fun M hM hMi hMd => ?_⟩
  obtain ⟨x, hx, hx0, hxB⟩ := hB M hM hMi hMd
  exact ⟨x, hx, hx0, hMi x hx, hxB⟩

end Value

/-! ### O'Meara 103:4: bases with Gram matrix in a finite set -/

section Induction

/-- A lattice contains a nonzero $\mathcal O_F$-multiple of every vector. -/
theorem exists_smul_mem_lattice {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) (x : Fin n → F) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ s • x ∈ L := by
  obtain ⟨d, hd0, hd, -⟩ := exists_global_bounds hL
  obtain ⟨e, he0, he⟩ := exists_smul_mem_intVec x
  exact ⟨d * e, mul_ne_zero hd0 he0, by rw [mul_smul]; exact hd _ he⟩

/-- **The inductive step of O'Meara 103:4:** for $Q$ on $F^{n+1}$, $c \ne 0$ and $\alpha \ne 0$, assuming the Gram-basis
statement in dimension $n$ (`IH`), there is a finite set $S$ of Gram matrices such that every integral lattice $M$ with
$c\,M^\# \subseteq M$ and a vector $x \in M$ with $Q(x) = \alpha$ has a basis in $M$ with Gram matrix in $S$. -/
@[kb "omeara1963" "§103, proof of 103:4, step 2, pp. 309–310"]
theorem gram_step (IH : ∀ Q' : QuadForm F n, Q'.Nondegenerate → ∀ c' : ℤ, c' ≠ 0 →
      ∃ S' : Set (Matrix (Fin n) (Fin n) F), S'.Finite ∧ ∀ M' : Submodule (𝓞 F) (Fin n → F), M'.IsLattice F →
        Lattices.IsIntegral Q' M' → IsDualBounded Q' M' c' → ∃ z : Fin n → Fin n → F, LinearIndependent F z ∧
          (∀ i, z i ∈ M') ∧ gramOf Q' z ∈ S')
    {Q : QuadForm F (n + 1)} (hQ : Q.Nondegenerate) {c : ℤ} (hc : c ≠ 0) (α : F) (hα : α ≠ 0) :
    ∃ S : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F), S.Finite ∧
      ∀ M : Submodule (𝓞 F) (Fin (n + 1) → F), M.IsLattice F → Lattices.IsIntegral Q M → IsDualBounded Q M c →
        (∃ x ∈ M, Q.eval x = α) → ∃ x : Fin (n + 1) → Fin (n + 1) → F, LinearIndependent F x ∧
          (∀ i, x i ∈ M) ∧ gramOf Q x ∈ S := by
  classical
  by_cases hy : ∃ y, Q.eval y = α
  swap
  · exact ⟨∅, Set.finite_empty, fun M _ _ _ ⟨x, _, hx⟩ => absurd ⟨x, hx⟩ hy⟩
  obtain ⟨y, hyα⟩ := hy
  -- the hyperplane `U = y^⊥`
  let ℓ : (Fin (n + 1) → F) →ₗ[F] F :=
    { toFun := fun v => bil Q v y
      map_add' := fun a b => bil_add_left Q a b y
      map_smul' := fun t a => bil_smul_left Q t a y }
  have hℓ : ∀ v, ℓ v = bil Q v y := fun _ => rfl
  have hyy : bil Q y y = 2 * α := by rw [bil_self, hyα]
  have h2α : (2 : F) * α ≠ 0 := mul_ne_zero two_ne_zero hα
  have hrange : LinearMap.range ℓ = ⊤ := by
    refine eq_top_iff.mpr fun t _ => ⟨(t / (2 * α)) • y, ?_⟩
    rw [hℓ, bil_smul_left, hyy, div_mul_cancel₀ _ h2α]
  set U := LinearMap.ker ℓ
  have hU : finrank F U = n := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
    change 1 + finrank F U = n + 1 at h
    omega
  let bU : Basis (Fin n) F U := Module.finBasisOfFinrankEq F U hU
  set u : Fin n → Fin (n + 1) → F := fun j => (bU j : Fin (n + 1) → F)
  have hu : LinearIndependent F u := bU.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have huU : ∀ j, bil Q (u j) y = 0 := fun j => (bU j).2
  set Um : Matrix (Fin (n + 1)) (Fin n) F := Matrix.of fun r j => u j r
  have hUm : ∀ z, Um *ᵥ z = ∑ j, z j • u j := by
    intro z; funext r; simp [Um, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hUmU : ∀ z, bil Q (Um *ᵥ z) y = 0 := by
    intro z; rw [hUm, bil_sum_left]; simp [huU]
  have hUminj : Function.Injective (Um *ᵥ ·) := by
    intro z z' h
    simp only [hUm] at h
    have := Fintype.linearIndependent_iff.mp hu (z - z') (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
    funext j; exact sub_eq_zero.mp (this j)
  have hdecomp : ∀ v, ∃ z, v = (bil Q v y / (2 * α)) • y + Um *ᵥ z := by
    intro v
    have hmem : v - (bil Q v y / (2 * α)) • y ∈ U := by
      change bil Q _ y = 0
      rw [bil_sub_left, bil_smul_left, hyy, div_mul_cancel₀ _ h2α, sub_self]
    refine ⟨bU.repr ⟨_, hmem⟩, ?_⟩
    rw [hUm]
    have h1 := congrArg Subtype.val (bU.sum_repr ⟨_, hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    change ∑ j, bU.repr ⟨_, hmem⟩ j • u j = _ at h1
    rw [h1]; abel
  -- the form on `U` in the coordinates `u`
  set Q' : QuadForm F n := QuadForm.ofQuadraticForm (Q.toQuadraticForm.comp (Matrix.mulVecLin Um))
  have hQ'eval : ∀ z, Q'.eval z = Q.eval (Um *ᵥ z) := by
    intro z
    rw [QuadForm.eval_ofQuadraticForm, QuadraticMap.comp_apply, Matrix.mulVecLin_apply,
      QuadForm.toQuadraticForm_apply]
  have hQ'bil : ∀ z z', bil Q' z z' = bil Q (Um *ᵥ z) (Um *ᵥ z') := by
    intro z z'
    have h1 := eval_add Q' z z'
    have h2 := eval_add Q (Um *ᵥ z) (Um *ᵥ z')
    rw [hQ'eval, hQ'eval, hQ'eval, mulVec_add] at h1
    linear_combination h2 - h1
  have hQ' : Q'.Nondegenerate := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    set w := Um *ᵥ z
    have hw0 : w ≠ 0 := fun h => hz0 (hUminj (by simp only [mulVec_zero]; exact h))
    have hbz : ∀ z', bil Q (Um *ᵥ z') w = 0 := fun z' => by
      rw [← hQ'bil, bil, hz, dotProduct_zero]
    have hby : bil Q y w = 0 := by rw [bil_comm]; exact hUmU z
    have hall : ∀ v, bil Q v w = 0 := by
      intro v
      obtain ⟨z', hz'⟩ := hdecomp v
      rw [hz', bil_add_left, bil_smul_left, hby, hbz, mul_zero, add_zero]
    have : Q.hessian *ᵥ w = 0 := by funext i; rw [← bil_single]; exact hall _
    exact hQ (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, this⟩)
  -- the dual bound for `M ∩ U`
  obtain ⟨kα, hkα0, hkα⟩ := exists_int_mul_mem ({(2 * α)⁻¹} : Finset F)
  have hkα' : (kα : F) * (2 * α)⁻¹ ∈ (algebraMap (𝓞 F) F).range := hkα _ (Finset.mem_singleton_self _)
  obtain ⟨S', hS'fin, hS'⟩ := IH Q' hQ' (c * kα) (mul_ne_zero hc hkα0)
  let blk : Matrix (Fin n) (Fin n) F → Matrix (Fin (n + 1)) (Fin (n + 1)) F := fun G' =>
    Matrix.of fun i j => Fin.cases (Fin.cases (2 * α) (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => G' i' j') j) i
  refine ⟨blk '' S', hS'fin.image _, fun M hM hMi hMd ⟨x₀, hx₀M, hx₀α⟩ => ?_⟩
  obtain ⟨γ, hγ, hγx⟩ := exists_orth_mulVec_eq Q (hx₀α.trans hyα.symm) (hx₀α ▸ hα)
  set M₁ := glImage γ M
  have hM₁ : M₁.IsLattice F := glImage_isLattice γ hM
  have hM₁i := isIntegral_glImage Q hMi hγ
  have hM₁d := isDualBounded_glImage Q hMd hγ
  have hyM₁ : y ∈ M₁ := hγx ▸ mulVec_mem_glImage hx₀M
  set K'' : Submodule (𝓞 F) (Fin n → F) := M₁.comap ((Matrix.mulVecLin Um).restrictScalars (𝓞 F))
  have hK''mem : ∀ z, z ∈ K'' ↔ Um *ᵥ z ∈ M₁ := fun z => Iff.rfl
  have hK''lat : K''.IsLattice F := by
    refine ⟨Submodule.fg_of_fg_map_injective ((Matrix.mulVecLin Um).restrictScalars (𝓞 F)) hUminj
      (Submodule.FG.of_le hM₁.fg (Submodule.map_comap_le _ _)), ?_⟩
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨s, hs0, hs⟩ := exists_smul_mem_lattice hM₁ (Um *ᵥ z)
    have hsz : s • z ∈ K'' := by rw [hK''mem, mulVec_smul]; exact hs
    have hs' : ιO s ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    have : z = (ιO s)⁻¹ • (s • z) := by
      rw [← algebraMap_smul F s z, smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsz)
  have hK''int : Lattices.IsIntegral Q' K'' := fun z hz => by
    have := hM₁i _ ((hK''mem z).mp hz)
    rwa [← QuadForm.eval, ← hQ'eval] at this
  have hK''dual : IsDualBounded Q' K'' (c * kα) := by
    intro z hz
    set w := Um *ᵥ z
    have hwy : bil Q w y = 0 := hUmU z
    have h2αO : 2 * α ∈ (algebraMap (𝓞 F) F).range := by rw [← hyy]; exact bil_mem Q hM₁i hyM₁ hyM₁
    have h2w : ∀ m ∈ M₁, bil Q ((2 * α) • w) m ∈ (algebraMap (𝓞 F) F).range := by
      intro m hm
      have hbO : bil Q m y ∈ (algebraMap (𝓞 F) F).range := bil_mem Q hM₁i hm hyM₁
      set m' := (2 * α) • m - (bil Q m y) • y
      have hm'M : m' ∈ M₁ := M₁.sub_mem (Steinitz.intSmul_mem h2αO hm) (Steinitz.intSmul_mem hbO hyM₁)
      have hm'U : bil Q m' y = 0 := by
        rw [bil_sub_left, bil_smul_left, bil_smul_left, hyy]; ring
      obtain ⟨z', hz'⟩ := hdecomp m'
      rw [hm'U, zero_div, zero_smul, zero_add] at hz'
      have hz'K : z' ∈ K'' := by rw [hK''mem, ← hz']; exact hm'M
      have := hz z' hz'K
      rw [hQ'bil, ← hz'] at this
      have e : bil Q w m' = bil Q ((2 * α) • w) m := by
        rw [bil_sub_right, bil_smul_right, bil_smul_right, bil_smul_left, hwy]; ring
      rwa [e] at this
    have h1 := hM₁d _ h2w
    rw [hK''mem]
    have e : Um *ᵥ ((c * kα) • z) = ((kα : F) * (2 * α)⁻¹) • (c • ((2 * α) • w)) := by
      rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, mulVec_smul, smul_smul, smul_smul]
      congr 1; push_cast; field_simp
    rw [e]; exact Steinitz.intSmul_mem hkα' h1
  obtain ⟨z, hzli, hzK, hzS⟩ := hS' K'' hK''lat hK''int hK''dual
  -- the basis `y, U z₀, …, U z_{n-1}` of `M₁`
  set x : Fin (n + 1) → Fin (n + 1) → F := Fin.cons y fun j => Um *ᵥ z j
  have hxli : LinearIndependent F x := by
    refine linearIndependent_finCons.mpr ⟨?_, ?_⟩
    · exact hzli.map' (Matrix.mulVecLin Um) (LinearMap.ker_eq_bot.mpr hUminj)
    · intro hspan
      have hle : Submodule.span F (Set.range fun j => Um *ᵥ z j) ≤ U :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hUmU (z j))
      have : bil Q y y = 0 := hle hspan
      rw [hyy] at this; exact h2α this
  have hxM : ∀ i, x i ∈ M₁ := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [x] using hyM₁
    · simpa [x] using (hK''mem _).mp (hzK j)
  have hxG : gramOf Q x = blk (gramOf Q' z) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [gramOf, blk, x, hyy]
    · simp [gramOf, blk, x, bil_comm Q y, hUmU]
    · simp [gramOf, blk, x, hUmU]
    · simp [gramOf, blk, x, hQ'bil]
  -- transport back by `γ⁻¹`
  have hγ' : γ⁻¹ ∈ orthGroup Q F := (orthGroup Q F).inv_mem hγ
  refine ⟨fun i => γ⁻¹.val *ᵥ x i, ?_, fun i => ?_, ⟨gramOf Q' z, hzS, ?_⟩⟩
  · exact hxli.map' (Matrix.mulVecLin γ⁻¹.val)
      (LinearMap.ker_eq_bot.mpr (mulVec_injective_of_det_ne_zero _
        (isUnit_iff_ne_zero.mp (γ⁻¹.isUnit.map Matrix.detMonoidHom))))
  · show γ⁻¹.val *ᵥ x i ∈ M
    obtain ⟨m, hm, hmx⟩ := hxM i
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hmx
    rw [← hmx, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    exact hm
  · rw [← hxG]
    ext i j
    simp only [gramOf, of_apply]
    exact (bil_isometry Q hγ' _ _).symm

/-- **Gram bases with Gram matrix in a finite set** (the induction of O'Meara 103:4): for nondegenerate $Q$ on $F^n$ and
$c \ne 0$ there is a finite set $S$ of $n \times n$ matrices such that every integral lattice $M$ with
$c\,M^\# \subseteq M$ contains an $F$-basis $x_0, \dots, x_{n-1}$ of $F^n$ whose Gram matrix $(B(x_i, x_j))$ lies in $S$. -/
@[kb "omeara1963" "§103, proof of 103:4, pp. 309–310"]
theorem exists_gram_basis : ∀ (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate → ∀ c : ℤ, c ≠ 0 →
    ∃ S : Set (Matrix (Fin n) (Fin n) F), S.Finite ∧ ∀ M : Submodule (𝓞 F) (Fin n → F), M.IsLattice F →
      Lattices.IsIntegral Q M → IsDualBounded Q M c → ∃ x : Fin n → Fin n → F, LinearIndependent F x ∧
        (∀ i, x i ∈ M) ∧ gramOf Q x ∈ S := by
  intro n
  induction n with
  | zero =>
    intro Q _ c _
    refine ⟨Set.univ, Set.toFinite _, fun M _ _ _ => ⟨fun i => i.elim0, linearIndependent_empty_type,
      fun i => i.elim0, Set.mem_univ _⟩⟩
  | succ n ih =>
    intro Q hQ c hc
    obtain ⟨Θ, hΘ, hΘ0, hΘM⟩ := exists_value_set (Nat.succ_pos n) hQ hc
    have hstep := fun α (hα : α ∈ Θ) => gram_step ih hQ hc α (fun h => hΘ0 (h ▸ hα))
    choose S hSfin hS using hstep
    refine ⟨⋃ α, ⋃ (h : α ∈ Θ), S α h, hΘ.biUnion' hSfin, fun M hM hMi hMd => ?_⟩
    obtain ⟨x, hx, hxΘ⟩ := hΘM M hM hMi hMd
    obtain ⟨b, hbli, hbM, hbS⟩ := hS _ hxΘ M hM hMi hMd ⟨x, hx, rfl⟩
    exact ⟨b, hbli, hbM, Set.mem_iUnion₂.mpr ⟨_, hxΘ, hbS⟩⟩

end Induction

/-! ### Rigidity and the finiteness of classes -/

section Classes

/-- **Lattices between $\mathcal O_F^n$ and $\delta^{-1}\mathcal O_F^n$ are finitely many** ($\delta \in \mathbb Z \setminus 0$): such a
lattice is determined by which of the finitely many vectors $\delta'^{-1}(\sum_k q_{ik}\omega_k)_i$, $0 \le q_{ik} < \delta' = |\delta|$,
it contains. -/
theorem finite_between {δ : ℤ} (hδ : δ ≠ 0) :
    {C : Submodule (𝓞 F) (Fin n → F) | intVec ≤ C ∧ ∀ c ∈ C, (δ : F) • c ∈ intVec}.Finite := by
  classical
  set m := δ.natAbs
  have hm : 0 < m := Int.natAbs_pos.mpr hδ
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  set R : Set (Fin n → F) := Set.range fun q : Fin n → OIdx F → Fin m =>
    fun i => (m : F)⁻¹ * ιO (∑ k, ((q i k : ℕ) : ℤ) • ω k)
  have hR : R.Finite := Set.finite_range _
  have key : ∀ C C' : Submodule (𝓞 F) (Fin n → F),
      (intVec ≤ C ∧ ∀ c ∈ C, (δ : F) • c ∈ intVec) → intVec ≤ C' →
      {r ∈ R | r ∈ C} = {r ∈ R | r ∈ C'} → C ≤ C' := by
    intro C C' hC hC' he c hc
    have hmc : (m : F) • c ∈ intVec := by
      have h1 := hC.2 c hc
      have e : (m : F) = ((|δ| : ℤ) : F) := by rw [← Int.natCast_natAbs, Int.cast_natCast]
      rw [e]
      rcases abs_choice δ with h | h <;> rw [h]
      · exact h1
      · rw [Int.cast_neg, neg_smul]; exact Submodule.neg_mem _ h1
    choose z hz using hmc
    choose w q hq hzq using fun i => exists_sub_mem_box m hm (z i)
    set r : Fin n → F := fun i => (m : F)⁻¹ * ιO (∑ k, q i k • ω k)
    have hrR : r ∈ R := by
      refine ⟨fun i k => ⟨(q i k).toNat, by have := hq i k; omega⟩, ?_⟩
      funext i
      simp only [r]
      congr 3
      funext k
      congr 1
      have := (hq i k).1
      simp [Int.toNat_of_nonneg this]
    set o : Fin n → F := fun i => ιO (w i)
    have ho : o ∈ intVec := fun i => ⟨w i, rfl⟩
    have hco : c = r + o := by
      funext i
      have h1 : (m : F) * c i = ιO (z i) := by rw [hz i]; rfl
      have h2 := congrArg ιO (hzq i)
      rw [map_add, map_mul, map_natCast, ← h1] at h2
      simp only [Pi.add_apply, r, o]
      field_simp
      linear_combination h2
    have hrC : r ∈ C := by
      have : r = c - o := by rw [hco]; abel
      rw [this]; exact C.sub_mem hc (hC.1 ho)
    have : r ∈ {r ∈ R | r ∈ C'} := he ▸ ⟨hrR, hrC⟩
    rw [hco]; exact C'.add_mem this.2 (hC' ho)
  refine Set.Finite.of_injOn (f := fun C => {r ∈ R | r ∈ C}) (t := {s | s ⊆ R})
    (fun C _ => fun r hr => hr.1) (fun C hC C' hC' he => ?_) hR.finite_subsets
  exact le_antisymm (key C C' hC hC'.1 he) (key C' C hC' hC.1 he.symm)

/-- The matrix with columns $x_0, \dots, x_{n-1}$. -/
def colMat (x : Fin n → Fin n → F) : Matrix (Fin n) (Fin n) F := Matrix.of fun r i => x i r

theorem colMat_mulVec_single (x : Fin n → Fin n → F) (i : Fin n) : colMat x *ᵥ Pi.single i 1 = x i := by
  funext r; simp [colMat]

variable {Q : QuadForm F n}

/-- **O'Meara 103:4 (finiteness of the class number):** for nondegenerate $Q$ on $F^n$ (definite or indefinite) and
$c \ne 0$, the integral lattices $M \subseteq F^n$ with $c\,M^\# \subseteq M$ fall into finitely many classes
(isometry classes under $O(V)(F)$). -/
@[kb "omeara1963" "§103, 103:4, p. 309; cassels1978 Ch. 9, Thm. 1.1, p. 128"]
theorem classes_finite (hQ : Q.Nondegenerate) {c : ℤ} (hc : c ≠ 0) :
    {cls : LatClass Q | ∃ M : Lat F n, Quotient.mk _ M = cls ∧ Lattices.IsIntegral Q M.1 ∧
      IsDualBounded Q M.1 c}.Finite := by
  classical
  obtain ⟨S, hSfin, hS⟩ := exists_gram_basis n Q hQ c hc
  -- a denominator for `G⁻¹`
  have hδex : ∀ G : Matrix (Fin n) (Fin n) F, ∃ δ : ℤ, δ ≠ 0 ∧ ∀ i j,
      (δ : F) * G⁻¹ i j ∈ (algebraMap (𝓞 F) F).range := fun G => by
    obtain ⟨δ, hδ, h⟩ := exists_int_mul_mem (Finset.univ.image fun ij : Fin n × Fin n => G⁻¹ ij.1 ij.2)
    exact ⟨δ, hδ, fun i j => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))⟩
  choose δ hδ0 hδ using hδex
  set Pairs : Set (Matrix (Fin n) (Fin n) F × Submodule (𝓞 F) (Fin n → F)) :=
    ⋃ G ∈ S, ({G} : Set _) ×ˢ {C | intVec ≤ C ∧ ∀ c ∈ C, (δ G : F) • c ∈ intVec}
  have hPairs : Pairs.Finite := hSfin.biUnion fun G _ => (Set.finite_singleton G).prod (finite_between (hδ0 G))
  let Pc : LatClass Q → Matrix (Fin n) (Fin n) F × Submodule (𝓞 F) (Fin n → F) → Prop := fun cls d =>
    ∃ M : Lat F n, Quotient.mk _ M = cls ∧ ∃ X : GL (Fin n) F,
      X.valᵀ * Q.hessian * X.val = d.1 ∧ glImage X⁻¹ M.1 = d.2
  have key : ∀ cls ∈ {cls : LatClass Q | ∃ M : Lat F n, Quotient.mk _ M = cls ∧ Lattices.IsIntegral Q M.1 ∧
      IsDualBounded Q M.1 c}, ∃ d ∈ Pairs, Pc cls d := by
    rintro _ ⟨M, rfl, hMi, hMd⟩
    obtain ⟨x, hxli, hxM, hxS⟩ := hS M.1 M.2 hMi hMd
    have hXu : IsUnit (colMat x) := Matrix.linearIndependent_col_iff_isUnit.mp hxli
    set X : GL (Fin n) F := hXu.unit
    have hXv : X.val = colMat x := rfl
    set G := gramOf Q x
    have hG : G = X.valᵀ * Q.hessian * X.val := by rw [hXv]; exact gramOf_eq Q x
    have hGdet : G.det ≠ 0 := by
      rw [hG, det_mul, det_mul, det_transpose]
      have := isUnit_iff_ne_zero.mp (X.isUnit.map Matrix.detMonoidHom)
      exact mul_ne_zero (mul_ne_zero this hQ) this
    refine ⟨(G, glImage X⁻¹ M.1), Set.mem_biUnion hxS ⟨rfl, ?_, ?_⟩, M, rfl, X, hG.symm, rfl⟩
    · -- `𝒪^n ⊆ X⁻¹ M`
      intro ξ hξ
      refine ⟨X.val *ᵥ ξ, ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := eq_sum_of_mem_intVec hξ
        rw [mulVec_sum]
        refine M.1.sum_mem fun i _ => ?_
        rw [mulVec_smul, hXv, colMat_mulVec_single]
        exact M.1.smul_mem _ (hxM i)
      · simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    · -- `δ X⁻¹ M ⊆ 𝒪^n`
      rintro _ ⟨m, hm, rfl⟩
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
      set v := X⁻¹.val *ᵥ m
      have hGv : G *ᵥ v = fun i => bil Q (x i) m := by
        funext i
        rw [hG, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_inv_mulVec, hXv]
        simp [colMat, mulVec, dotProduct, bil]
      have hGvO : ∀ i, (G *ᵥ v) i ∈ (algebraMap (𝓞 F) F).range := fun i => by
        rw [hGv]; exact bil_mem Q hMi (hxM i) hm
      have hvv : v = G⁻¹ *ᵥ (G *ᵥ v) := by
        rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hGdet), one_mulVec]
      intro i
      rw [hvv, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum]
      refine Subring.sum_mem _ fun j _ => ?_
      rw [← mul_assoc]
      exact Subring.mul_mem _ (hδ G i j) (hGvO j)
  choose! f hfP hfPc using key
  refine Set.Finite.of_injOn (f := f) (fun cls hcls => hfP cls hcls) (fun c₁ hc₁ c₂ hc₂ he => ?_) hPairs
  obtain ⟨M₁, rfl, X₁, hG₁, hC₁⟩ := hfPc c₁ hc₁
  obtain ⟨M₂, rfl, X₂, hG₂, hC₂⟩ := hfPc _ hc₂
  rw [he] at hG₁ hC₁
  apply Quotient.sound
  refine ⟨X₂ * X₁⁻¹, ?_, ?_⟩
  · rw [mem_orthGroup, hessian_map_id, Units.val_mul, transpose_mul]
    have h1 : X₁.val * X₁⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (X₁⁻¹).valᵀ * X₂.valᵀ * Q.hessian * (X₂.val * X₁⁻¹.val)
        = (X₁⁻¹).valᵀ * (X₂.valᵀ * Q.hessian * X₂.val) * X₁⁻¹.val := by simp only [Matrix.mul_assoc]
      _ = (X₁⁻¹).valᵀ * (X₁.valᵀ * Q.hessian * X₁.val) * X₁⁻¹.val := by rw [hG₂, hG₁]
      _ = (X₁.val * X₁⁻¹.val)ᵀ * Q.hessian * (X₁.val * X₁⁻¹.val) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Q.hessian := by rw [h1]; simp
  · change glImage (X₂ * X₁⁻¹) M₁.1 = M₂.1
    rw [glImage_mul, hC₁, ← hC₂, ← glImage_mul, mul_inv_cancel, glImage_one]

/-- **The genus of an integral lattice has finitely many classes, for every nondegenerate $Q$** (O'Meara 103:4): the
dual bound $c\,M^\# \subseteq M$ holds uniformly on the genus (`exists_dual_zsmul_mem`) and integrality is a genus
invariant (`SameGenus.isIntegral`). This removes the hypothesis `IsTotallyPosDef` of `genusClasses_finite`. -/
@[kb "omeara1963" "§103, 103:4, p. 309 ('in particular, the number of proper classes in a genus is finite')"]
theorem genusClasses_finite_of_nondegenerate (hQ : Q.Nondegenerate) (L : Lat F n)
    (hLi : Lattices.IsIntegral Q L.1) : (genusClasses Q L).Finite := by
  obtain ⟨c, hc, hdual⟩ := exists_dual_zsmul_mem Q hQ L.2
  refine (classes_finite hQ hc).subset ?_
  rintro _ ⟨M, rfl, hgen⟩
  exact ⟨M, rfl, hgen.isIntegral Q hLi, fun x hx => hdual M.1 M.2 hgen x hx⟩

/-- **Consistency with the earlier result:** the totally definite case `genusClasses_finite` (proved there by Hermite
reduction of the trace form) also follows from the general theorem. -/
theorem genusClasses_finite_of_totallyPosDef (hQ : IsTotallyPosDef Q) (L : Lat F n)
    (hLi : Lattices.IsIntegral Q L.1) : (genusClasses Q L).Finite :=
  genusClasses_finite_of_nondegenerate hQ.nondegenerate L hLi

end Classes

/-! ### Dropping integrality: rescaling the form -/

section Scaling

variable (Q : QuadForm F n)

theorem hessian_smul (a : F) : (a • Q).hessian = a • Q.hessian := by
  simp [QuadForm.hessian, Matrix.transpose_smul, smul_add]

theorem evalIn_smul_form (a : F) (x : Fin n → F) : (a • Q).evalIn F x = a * Q.evalIn F x := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, QuadForm.smul_coeff]
  simp [Matrix.smul_mulVec, dotProduct_smul]

/-- **Rescaling the form does not change $O(V)$:** $O(aQ)(R) = O(Q)(R)$ for $a \ne 0$ in $F$ and any $F$-algebra $R$. -/
theorem orthGroup_smul {a : F} (ha : a ≠ 0) (R : Type*) [CommRing R] [Algebra F R] :
    orthGroup (a • Q) R = orthGroup Q R := by
  ext g
  rw [mem_orthGroup, mem_orthGroup, hessian_smul]
  have hmap : (a • Q.hessian).map (algebraMap F R) = algebraMap F R a • Q.hessian.map (algebraMap F R) := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul, map_mul]
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul]
  have hu : IsUnit (algebraMap F R a) := (IsUnit.mk0 a ha).map _
  exact ⟨fun h => hu.smul_left_cancel.mp h, fun h => by rw [h]⟩

theorem isIsometric_smul_iff {a : F} (ha : a ≠ 0) (L M : Submodule (𝓞 F) (Fin n → F)) :
    IsIsometric (a • Q) L M ↔ IsIsometric Q L M := by
  simp only [IsIsometric, orthGroup_smul Q ha]

theorem sameGenus_smul_iff {a : F} (ha : a ≠ 0) (L M : Submodule (𝓞 F) (Fin n → F)) :
    SameGenus (a • Q) L M ↔ SameGenus Q L M := by
  simp only [SameGenus, orthGroup_smul Q ha]

/-- **Every lattice is integral for a rescaled form:** there is $a \ne 0$ with $aQ(L) \subseteq \mathcal O_F$
($a = e\,d^2$, $dL \subseteq \mathcal O_F^n$, $e\,c_{ij} \in \mathcal O_F$). -/
theorem exists_smul_isIntegral {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    ∃ a : F, a ≠ 0 ∧ Lattices.IsIntegral (a • Q) L := by
  classical
  obtain ⟨d, hd0, -, hd⟩ := exists_global_bounds hL
  obtain ⟨e, he0, he⟩ := exists_int_mul_mem (Finset.univ.image fun ij : Fin n × Fin n => Q.coeff ij.1 ij.2)
  have he' : ∀ i j, (e : F) * Q.coeff i j ∈ (algebraMap (𝓞 F) F).range := fun i j =>
    he _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  have hd' : ιO d ≠ 0 := by rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  refine ⟨(e : F) * ιO d ^ 2, mul_ne_zero (by exact_mod_cast he0) (pow_ne_zero _ hd'), fun x hx => ?_⟩
  have hdx := hd x hx
  rw [evalIn_smul_form, mul_assoc, ← evalIn_smul' Q (ιO d) x, algebraMap_smul]
  set y := d • x
  rw [QuadForm.evalIn, Finset.mul_sum]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  split_ifs
  · rw [Algebra.algebraMap_self, RingHom.id_apply, ← mul_assoc, ← mul_assoc]
    exact Subring.mul_mem _ (Subring.mul_mem _ (he' i j) (hdx i)) (hdx j)
  · rw [mul_zero]; exact Subring.zero_mem _

/-- **Finiteness of the class number of every genus over a number field** (O'Meara 103:4, as used in 104:1): for every
nondegenerate $Q$ on $F^n$ (definite or indefinite) and **every** lattice $L$ (integral or not), $\mathrm{gen}(L)$
contains only finitely many classes. Rescale $Q$ by $a \ne 0$ with $aQ(L)$ integral; $O(aQ) = O(Q)$, so classes and genera
are unchanged. -/
@[kb "omeara1963" "§103, 103:4, p. 309"]
theorem genusClasses_finite_nf (hQ : Q.Nondegenerate) (L : Lat F n) : (genusClasses Q L).Finite := by
  obtain ⟨a, ha, hLi⟩ := exists_smul_isIntegral Q L.2
  have hQa : (a • Q).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [hessian_smul, det_smul]
    exact mul_ne_zero (pow_ne_zero _ ha) hQ
  have hfin := genusClasses_finite_of_nondegenerate hQa L hLi
  let φ : LatClass Q → LatClass (a • Q) :=
    Quotient.map id fun M M' h => (isIsometric_smul_iff Q ha M.1 M'.1).mpr h
  refine Set.Finite.of_injOn (f := φ) (t := genusClasses (a • Q) L) ?_ ?_ hfin
  · rintro _ ⟨M, rfl, hgen⟩
    exact ⟨M, rfl, (sameGenus_smul_iff Q ha L.1 M.1).mpr hgen⟩
  · rintro _ ⟨M, rfl, -⟩ _ ⟨M', rfl, -⟩ he
    apply Quotient.sound
    exact (isIsometric_smul_iff Q ha M.1 M'.1).mp (Quotient.exact he)

/-- **Class representatives of a genus (the input of O'Meara 104:1):** for nondegenerate $Q$ and any lattice $L$ there
are finitely many lattices $L_1, \dots, L_h$ in $\mathrm{gen}(L)$ such that every lattice in $\mathrm{gen}(L)$ is isometric
to one of them. -/
@[kb "omeara1963" "§103, 103:4, p. 309; §104, proof of 104:1, p. 311 (L_1, …, L_h one from each class in gen L)"]
theorem exists_genus_reps (hQ : Q.Nondegenerate) (L : Lat F n) :
    ∃ s : Finset (Lat F n), (∀ M ∈ s, SameGenus Q L.1 M.1) ∧
      ∀ M : Lat F n, SameGenus Q L.1 M.1 → ∃ M' ∈ s, IsIsometric Q M.1 M'.1 := by
  classical
  have h := genusClasses_finite_nf Q hQ L
  let rep : genusClasses Q L → Lat F n := fun c => c.2.choose
  have hrep : ∀ c : genusClasses Q L, Quotient.mk _ (rep c) = c.1 ∧ SameGenus Q L.1 (rep c).1 :=
    fun c => c.2.choose_spec
  refine ⟨h.toFinset.attach.image fun c => rep ⟨c.1, h.mem_toFinset.mp c.2⟩, ?_, fun M hM => ?_⟩
  · intro M hM
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hM
    exact (hrep _).2
  · have hc : Quotient.mk (latSetoid Q) M ∈ genusClasses Q L := ⟨M, rfl, hM⟩
    refine ⟨rep ⟨_, hc⟩, Finset.mem_image.mpr ⟨⟨_, h.mem_toFinset.mpr hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    exact IsIsometric.symm Q (Quotient.exact (hrep ⟨_, hc⟩).1)

end Scaling

end QuadFormsKB.Lattices.ClassFin
