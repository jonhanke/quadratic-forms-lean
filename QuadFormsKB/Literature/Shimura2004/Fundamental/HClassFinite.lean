/-
# Shimura 2004, Theorem 11.6 (i), p. 104: finiteness of $H\backslash H_{\mathbb A}/(H_{\mathbb A}\cap C)$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 11.6 (i), p. 104, which
uses the finiteness of the class number of $H = SO^\varphi(W)$, $W = (Fh)^\perp$, relative to the open compact
subgroup $H_{\mathbb A} \cap C$ (§9.3). The classical input is O'Meara, *Introduction to Quadratic Forms* (1963),
103:4, p. 309 (finiteness of the number of classes in a genus), in the library as `ClassFin.exists_gram_basis`.

**Statement.** The named input `HClassNumberFinite`: for every number field $F$, nondegenerate $\varphi$ on $F^n$
with $n > 2$, lattice $L$ and $h$ with $\varphi[h] \ne 0$, the double coset space
$H\backslash H_{\mathbf h}/(H_{\mathbf h}\cap C)$ (`hDoubleCosets`) is finite.

**Route.**
1. *(Reduction, `dcToClass`)* The map $H\eta(H_{\mathbf h}\cap C) \mapsto$ the $H$-class of $\eta L$ is a well defined
   injection from the double coset space into the set of $H$-classes of the $H$-genus of $L$
   (`finite_hDoubleCosets_of_finite_classes`).
2. *(Finite number of classes fixing a vector, `exists_finite_fix_reps`)* Fix a vector $y$ with $\varphi[y] \ne 0$
   and an integer $c \ne 0$. Then the integral lattices $M \ni y$ with $c\,M^\# \subseteq M$ fall into finitely many
   orbits under the stabilizer $O(V)_y$ of $y$ in $O(V)(F)$. This is O'Meara's proof of 103:4 run with the first basis
   vector pinned to $y$ (`gram_step_fix`: the induction step of `ClassFin.gram_step` without moving $y$ by an
   isometry; the induction hypothesis in dimension $n-1$ is `ClassFin.exists_gram_basis`), followed by the rigidity step
   of `ClassFin.classes_finite` (equal Gram matrix and equal lattice in coordinates give an isometry fixing $y$).
   This replaces the route through coordinates on $W$, the genus of $L \cap W$ and the finite fibre over it.
3. *(The $H$-genus, `finite_hClassesInHGenus`)* Rescale $\varphi$ by $a \in F^\times$ so that $L$ is integral (this
   does not change $O(V)$, `ClassFin.orthGroup_smul`). Every $M = \eta L$ in the $H$-genus lies in the genus of $L$
   (so is integral and satisfies $c\,M^\# \subseteq M$ for one $c$, `exists_dual_zsmul_mem`), and contains the fixed
   vector $y = s h \in L$, because $\eta h = h$ at every prime. By step 2, $M = \sigma M_0$ with $M_0$ in a finite set
   $Z$ and $\sigma \in O(V)_h$. Two lattices $\sigma M_0$, $\sigma' M_0$ with $\det\sigma = \det\sigma'$ differ by
   $\sigma'\sigma^{-1} \in SO(V)_h = H$, so there are at most $2\,\#Z$ classes.

**Proves** (standard axioms only, no `sorry`): `finite_hClassesInHGenus`; the input `hClassNumberFinite`
(unconditionally); and `theorem11_6_i_of_local`, `fundamentalTheorem11_6_of_local`, now unconditional (their
only input `LocalTheorem10_5` is proved, `Theorem105.lean`).
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.Theorem116
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Module Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Lattices.ClassFin QuadFormsKB.Tamagawa

attribute [local instance] invTwo latAction

variable {F : Type} [Field F] [NumberField F]

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### Step 2: Gram bases with the first vector pinned to $y$ -/

/-- **The inductive step of O'Meara 103:4 with a fixed vector** (`ClassFin.gram_step` without moving the vector by
an isometry): for $\varphi$ nondegenerate on $F^{m+1}$, $c \ne 0$ and $y$ with $\varphi[y] \ne 0$, there is a finite
set $S$ of Gram matrices such that every integral lattice $M \ni y$ with $c\,M^\# \subseteq M$ has an $F$-basis
$x_0 = y, x_1, \dots, x_m$ in $M$ with Gram matrix $(B(x_i, x_j))$ in $S$. -/
theorem gram_step_fix {m : ℕ} {Q : QuadForm F (m + 1)} (hQ : Q.Nondegenerate) {c : ℤ} (hc : c ≠ 0)
    (y : Fin (m + 1) → F) (hy : Q.eval y ≠ 0) :
    ∃ S : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) F), S.Finite ∧
      ∀ M : Submodule (𝓞 F) (Fin (m + 1) → F), M.IsLattice F → Lattices.IsIntegral Q M →
        IsDualBounded Q M c → y ∈ M → ∃ x : Fin (m + 1) → Fin (m + 1) → F, LinearIndependent F x ∧
          (∀ i, x i ∈ M) ∧ x 0 = y ∧ gramOf Q x ∈ S := by
  classical
  obtain ⟨α, hα, hyα⟩ : ∃ α, α ≠ 0 ∧ Q.eval y = α := ⟨_, hy, rfl⟩
  -- the hyperplane `U = y^⊥`
  let ℓ : (Fin (m + 1) → F) →ₗ[F] F :=
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
  have hU : finrank F U = m := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
    change 1 + finrank F U = m + 1 at h
    omega
  let bU : Basis (Fin m) F U := Module.finBasisOfFinrankEq F U hU
  set u : Fin m → Fin (m + 1) → F := fun j => (bU j : Fin (m + 1) → F)
  have hu : LinearIndependent F u := bU.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have huU : ∀ j, bil Q (u j) y = 0 := fun j => (bU j).2
  set Um : Matrix (Fin (m + 1)) (Fin m) F := Matrix.of fun r j => u j r
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
  set Q' : QuadForm F m := QuadForm.ofQuadraticForm (Q.toQuadraticForm.comp (Matrix.mulVecLin Um))
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
  obtain ⟨S', hS'fin, hS'⟩ := exists_gram_basis m Q' hQ' (c * kα) (mul_ne_zero hc hkα0)
  let blk : Matrix (Fin m) (Fin m) F → Matrix (Fin (m + 1)) (Fin (m + 1)) F := fun G' =>
    Matrix.of fun i j => Fin.cases (Fin.cases (2 * α) (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => G' i' j') j) i
  refine ⟨blk '' S', hS'fin.image _, fun M hM hMi hMd hyM => ?_⟩
  set K'' : Submodule (𝓞 F) (Fin m → F) := M.comap ((Matrix.mulVecLin Um).restrictScalars (𝓞 F))
  have hK''mem : ∀ z, z ∈ K'' ↔ Um *ᵥ z ∈ M := fun z => Iff.rfl
  have hK''lat : K''.IsLattice F := by
    refine ⟨Submodule.fg_of_fg_map_injective ((Matrix.mulVecLin Um).restrictScalars (𝓞 F)) hUminj
      (Submodule.FG.of_le hM.fg (Submodule.map_comap_le _ _)), ?_⟩
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨s, hs0, hs⟩ := exists_smul_mem_lattice hM (Um *ᵥ z)
    have hsz : s • z ∈ K'' := by rw [hK''mem, mulVec_smul]; exact hs
    have hs' : ιO s ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    have : z = (ιO s)⁻¹ • (s • z) := by
      rw [← algebraMap_smul F s z, smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsz)
  have hK''int : Lattices.IsIntegral Q' K'' := fun z hz => by
    have := hMi _ ((hK''mem z).mp hz)
    rwa [← QuadForm.eval, ← hQ'eval] at this
  have hK''dual : IsDualBounded Q' K'' (c * kα) := by
    intro z hz
    set w := Um *ᵥ z
    have hwy : bil Q w y = 0 := hUmU z
    have h2αO : 2 * α ∈ (algebraMap (𝓞 F) F).range := by rw [← hyy]; exact bil_mem Q hMi hyM hyM
    have h2w : ∀ m ∈ M, bil Q ((2 * α) • w) m ∈ (algebraMap (𝓞 F) F).range := by
      intro m hm
      have hbO : bil Q m y ∈ (algebraMap (𝓞 F) F).range := bil_mem Q hMi hm hyM
      set m' := (2 * α) • m - (bil Q m y) • y
      have hm'M : m' ∈ M := M.sub_mem (Steinitz.intSmul_mem h2αO hm) (Steinitz.intSmul_mem hbO hyM)
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
    have h1 := hMd _ h2w
    rw [hK''mem]
    have e : Um *ᵥ ((c * kα) • z) = ((kα : F) * (2 * α)⁻¹) • (c • ((2 * α) • w)) := by
      rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, mulVec_smul, smul_smul, smul_smul]
      congr 1; push_cast; field_simp
    rw [e]; exact Steinitz.intSmul_mem hkα' h1
  obtain ⟨z, hzli, hzK, hzS⟩ := hS' K'' hK''lat hK''int hK''dual
  -- the basis `y, U z₀, …, U z_{m-1}` of `M`
  set x : Fin (m + 1) → Fin (m + 1) → F := Fin.cons y fun j => Um *ᵥ z j
  have hxli : LinearIndependent F x := by
    refine linearIndependent_finCons.mpr ⟨?_, ?_⟩
    · exact hzli.map' (Matrix.mulVecLin Um) (LinearMap.ker_eq_bot.mpr hUminj)
    · intro hspan
      have hle : Submodule.span F (Set.range fun j => Um *ᵥ z j) ≤ U :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hUmU (z j))
      have : bil Q y y = 0 := hle hspan
      rw [hyy] at this; exact h2α this
  have hxM : ∀ i, x i ∈ M := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [x] using hyM
    · simpa [x] using (hK''mem _).mp (hzK j)
  have hxG : gramOf Q x = blk (gramOf Q' z) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [gramOf, blk, x, hyy]
    · simp [gramOf, blk, x, bil_comm Q y, hUmU]
    · simp [gramOf, blk, x, hUmU]
    · simp [gramOf, blk, x, hQ'bil]
  exact ⟨x, hxli, hxM, by simp [x], ⟨gramOf Q' z, hzS, hxG.symm⟩⟩

/-- **Finitely many orbits of lattices under the stabilizer of a vector** (O'Meara 103:4 with a pinned vector): for
$\varphi$ nondegenerate on $F^{m+1}$, $c \ne 0$ and $y$ with $\varphi[y] \ne 0$ there is a finite set $Z$ of
$\mathcal O_F$-submodules such that every integral lattice $M \ni y$ with $c\,M^\# \subseteq M$ is $\sigma M_0$ for some
$M_0 \in Z$ and $\sigma \in O(V)(F)$ with $\sigma y = y$. -/
@[kb "omeara1963" "§103, 103:4, p. 309 (finiteness of classes; version with a fixed vector, used for Shimura 2004, Thm. 11.6 (i), p. 104)"]
theorem exists_finite_fix_reps {m : ℕ} {Q : QuadForm F (m + 1)} (hQ : Q.Nondegenerate) {c : ℤ} (hc : c ≠ 0)
    (y : Fin (m + 1) → F) (hy : Q.eval y ≠ 0) :
    ∃ Z : Set (Submodule (𝓞 F) (Fin (m + 1) → F)), Z.Finite ∧
      ∀ M : Submodule (𝓞 F) (Fin (m + 1) → F), M.IsLattice F → Lattices.IsIntegral Q M →
        IsDualBounded Q M c → y ∈ M →
          ∃ M₀ ∈ Z, ∃ σ : GL (Fin (m + 1)) F, σ ∈ orthGroup Q F ∧ σ.val *ᵥ y = y ∧ glImage σ M₀ = M := by
  classical
  obtain ⟨S, hSfin, hS⟩ := gram_step_fix hQ hc y hy
  -- a denominator for `G⁻¹`
  have hδex : ∀ G : Matrix (Fin (m + 1)) (Fin (m + 1)) F, ∃ δ : ℤ, δ ≠ 0 ∧ ∀ i j,
      (δ : F) * G⁻¹ i j ∈ (algebraMap (𝓞 F) F).range := fun G => by
    obtain ⟨δ, hδ, h⟩ := exists_int_mul_mem (Finset.univ.image fun ij : Fin (m + 1) × Fin (m + 1) => G⁻¹ ij.1 ij.2)
    exact ⟨δ, hδ, fun i j => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))⟩
  choose δ hδ0 hδ using hδex
  set Pairs : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) F × Submodule (𝓞 F) (Fin (m + 1) → F)) :=
    ⋃ G ∈ S, ({G} : Set _) ×ˢ {C | intVec ≤ C ∧ ∀ c ∈ C, (δ G : F) • c ∈ intVec}
  have hPairs : Pairs.Finite := hSfin.biUnion fun G _ => (Set.finite_singleton G).prod (finite_between (hδ0 G))
  let Pset : Set (Submodule (𝓞 F) (Fin (m + 1) → F)) :=
    {M | M.IsLattice F ∧ Lattices.IsIntegral Q M ∧ IsDualBounded Q M c ∧ y ∈ M}
  have key : ∀ M ∈ Pset, ∃ d ∈ Pairs, ∃ X : GL (Fin (m + 1)) F,
      X.valᵀ * Q.hessian * X.val = d.1 ∧ glImage X⁻¹ M = d.2 ∧ X.val *ᵥ Pi.single 0 1 = y := by
    rintro M ⟨hM, hMi, hMd, hyM⟩
    obtain ⟨x, hxli, hxM, hx0, hxS⟩ := hS M hM hMi hMd hyM
    have hXu : IsUnit (colMat x) := Matrix.linearIndependent_col_iff_isUnit.mp hxli
    set X : GL (Fin (m + 1)) F := hXu.unit
    have hXv : X.val = colMat x := rfl
    set G := gramOf Q x
    have hG : G = X.valᵀ * Q.hessian * X.val := by rw [hXv]; exact gramOf_eq Q x
    have hGdet : G.det ≠ 0 := by
      rw [hG, det_mul, det_mul, det_transpose]
      have := isUnit_iff_ne_zero.mp (X.isUnit.map Matrix.detMonoidHom)
      exact mul_ne_zero (mul_ne_zero this hQ) this
    refine ⟨(G, glImage X⁻¹ M), Set.mem_biUnion hxS ⟨rfl, ?_, ?_⟩, X, hG.symm, rfl, ?_⟩
    · -- `𝒪^n ⊆ X⁻¹ M`
      intro ξ hξ
      refine ⟨X.val *ᵥ ξ, ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := eq_sum_of_mem_intVec hξ
        rw [mulVec_sum]
        refine M.sum_mem fun i _ => ?_
        rw [mulVec_smul, hXv, colMat_mulVec_single]
        exact M.smul_mem _ (hxM i)
      · simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    · -- `δ X⁻¹ M ⊆ 𝒪^n`
      rintro _ ⟨m', hm, rfl⟩
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
      set v := X⁻¹.val *ᵥ m'
      have hGv : G *ᵥ v = fun i => bil Q (x i) m' := by
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
    · rw [hXv, colMat_mulVec_single, hx0]
  choose! f hfP hfPc using key
  let g : Matrix (Fin (m + 1)) (Fin (m + 1)) F × Submodule (𝓞 F) (Fin (m + 1) → F) →
      Submodule (𝓞 F) (Fin (m + 1) → F) := fun d => if h : ∃ M ∈ Pset, f M = d then h.choose else ⊥
  refine ⟨g '' Pairs, hPairs.image g, fun M hM hMi hMd hyM => ?_⟩
  have hMPset : M ∈ Pset := ⟨hM, hMi, hMd, hyM⟩
  have hex : ∃ M' ∈ Pset, f M' = f M := ⟨M, hMPset, rfl⟩
  have hg : g (f M) = hex.choose := dif_pos hex
  obtain ⟨hM'Pset, hM'f⟩ := hex.choose_spec
  refine ⟨g (f M), ⟨f M, hfP M hMPset, rfl⟩, ?_⟩
  rw [hg]
  obtain ⟨X₁, hG₁, hC₁, hX₁⟩ := hfPc _ hM'Pset
  obtain ⟨X₂, hG₂, hC₂, hX₂⟩ := hfPc M hMPset
  rw [hM'f] at hG₁ hC₁
  refine ⟨X₂ * X₁⁻¹, ?_, ?_, ?_⟩
  · rw [mem_orthGroup, hessian_map_id, Units.val_mul, transpose_mul]
    have h1 : X₁.val * X₁⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (X₁⁻¹).valᵀ * X₂.valᵀ * Q.hessian * (X₂.val * X₁⁻¹.val)
        = (X₁⁻¹).valᵀ * (X₂.valᵀ * Q.hessian * X₂.val) * X₁⁻¹.val := by simp only [Matrix.mul_assoc]
      _ = (X₁⁻¹).valᵀ * (X₁.valᵀ * Q.hessian * X₁.val) * X₁⁻¹.val := by rw [hG₂, hG₁]
      _ = (X₁.val * X₁⁻¹.val)ᵀ * Q.hessian * (X₁.val * X₁⁻¹.val) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Q.hessian := by rw [h1]; simp
  · have h3 : X₁⁻¹.val *ᵥ y = Pi.single 0 1 := by
      conv_lhs => rw [← hX₁]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [Units.val_mul, ← mulVec_mulVec, h3, hX₂]
  · rw [glImage_mul, hC₁, ← hC₂, ← glImage_mul, mul_inv_cancel, glImage_one]

/-! ### Step 3: the $H$-genus -/

/-- The determinant of an element of $O(V)(F)$ is $\pm 1$. -/
theorem det_eq_one_or_neg_one_of_fix {m : ℕ} {Q : QuadForm F m} (hQ : Q.Nondegenerate) {σ : GL (Fin m) F}
    (hσ : σ ∈ orthGroup Q F) : σ.val.det = 1 ∨ σ.val.det = -1 := by
  have h := congrArg Matrix.det ((mem_orthGroup Q).1 hσ)
  rw [hessian_map_id Q, det_mul, det_mul, det_transpose] at h
  have hd : Q.hessian.det ≠ 0 := hQ
  have : σ.val.det * σ.val.det = 1 := by
    apply mul_right_cancel₀ hd
    linear_combination h
  exact mul_self_eq_one_iff.mp this

/-- **Finiteness of the number of $H$-classes in the $H$-genus** (Shimura 2004, p. 104; the class number of
$H = SO^\varphi(W)$ relative to $H_{\mathbf h} \cap C$). See the module docstring for the proof. -/
theorem finite_hClassesInHGenus {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : 2 < n) (L : Lat F n)
    (h : Fin n → F) (hh : Q.eval h ≠ 0) : Finite (hClassesInHGenus Q h L) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- rescale so that `L` is integral
  obtain ⟨a, ha, hLi⟩ := exists_smul_isIntegral Q L.2
  have hQa : (a • Q).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [hessian_smul, det_smul]
    exact mul_ne_zero (pow_ne_zero _ ha) hQ
  obtain ⟨c, hc, hdual⟩ := exists_dual_zsmul_mem (a • Q) hQa L.2
  -- the pinned vector `y = c₀ h ∈ L`
  obtain ⟨s, hs0, hsL⟩ := exists_smul_mem_lattice L.2 h
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : F, c₀ = ιO s := ⟨_, rfl⟩
  have hc₀ : c₀ ≠ 0 := by
    rw [hc₀def, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact hs0
  obtain ⟨y, hydef⟩ : ∃ y : Fin (m + 1) → F, y = c₀ • h := ⟨_, rfl⟩
  have hyL : y ∈ L.1 := by
    rw [hydef, hc₀def, algebraMap_smul F s h]; exact hsL
  have hya : (a • Q).eval y ≠ 0 := by
    have h1 : (a • Q).eval y = a * Q.eval y := evalIn_smul_form Q a y
    have h2 : Q.eval y = c₀ ^ 2 * Q.eval h := by rw [hydef]; exact eval_smul Q c₀ h
    rw [h1, h2]
    exact mul_ne_zero ha (mul_ne_zero (pow_ne_zero _ hc₀) hh)
  obtain ⟨Z, hZ, hZspec⟩ := exists_finite_fix_reps hQa hc y hya
  -- every lattice of the `H`-genus is `σ z` with `z ∈ Z` and `σ ∈ O(V)_h`
  have key : ∀ M : hGenus Q h L, ∃ z ∈ Z, ∃ σ : GL (Fin (m + 1)) F, σ ∈ orthGroup Q F ∧
      σ.val *ᵥ h = h ∧ glImage σ z = M.1.1 := by
    rintro ⟨M, η, hη, rfl⟩
    have hloc : ∀ v, loc v (η • L).1 =
        locAct v ((η v : orthGroup Q _) : GL (Fin (m + 1)) _) (loc v L.1) := fun v => loc_latSMul Q η L v
    have hgen : SameGenus Q L.1 (η • L).1 := fun v => ⟨((η v : orthGroup Q _) : GL _ _), (η v).2, (hloc v).symm⟩
    have hgen' : SameGenus (a • Q) L.1 (η • L).1 := (sameGenus_smul_iff Q ha L.1 (η • L).1).2 hgen
    have hNi : Lattices.IsIntegral (a • Q) (η • L).1 := hgen'.isIntegral (a • Q) hLi
    have hNd : IsDualBounded (a • Q) (η • L).1 c := fun x hx => hdual (η • L).1 (η • L).2 hgen' x hx
    have hyN : y ∈ (η • L).1 := by
      rw [mem_iff_forall_loc (η • L).2]
      intro v
      rw [hloc v, mem_locAct]
      refine ⟨locVec v y, locVec_mem_loc v hyL, ?_⟩
      have hfix : ((η v : orthGroup Q _) : GL (Fin (m + 1)) _).val *ᵥ
          (fun i => algebraMap F (v.adicCompletion F) (h i)) =
          fun i => algebraMap F (v.adicCompletion F) (h i) := hη.2 v
      have hv : locVec v y = (algebraMap F (v.adicCompletion F) c₀) •
          (fun i => algebraMap F (v.adicCompletion F) (h i)) := by
        funext i
        simp [hydef, locVec_apply, map_mul]
      rw [hv, mulVec_smul, hfix]
    obtain ⟨z, hzZ, σ, hσ, hσy, hσz⟩ := hZspec (η • L).1 (η • L).2 hNi hNd hyN
    have hσQ : σ ∈ orthGroup Q F := by rwa [orthGroup_smul Q ha F] at hσ
    have hσh : σ.val *ᵥ h = h := by
      have h1 : c₀ • (σ.val *ᵥ h) = c₀ • h := by
        rw [← mulVec_smul, ← hydef]; exact hσy
      exact smul_right_injective (Fin (m + 1) → F) hc₀ h1
    exact ⟨z, hzZ, σ, hσQ, hσh, hσz⟩
  -- the classes represented by `σ z` with `det σ = 1` (resp. `≠ 1`)
  let C : Submodule (𝓞 F) (Fin (m + 1) → F) → Bool → Set (hClassesInHGenus Q h L) := fun z b =>
    {k | ∃ (M : hGenus Q h L) (σ : GL (Fin (m + 1)) F), σ ∈ orthGroup Q F ∧ σ.val *ᵥ h = h ∧
      glImage σ z = M.1.1 ∧ decide (σ.val.det = 1) = b ∧ (Quot.mk _ M : hClassesInHGenus Q h L) = k}
  have hsub : ∀ z b, (C z b).Subsingleton := by
    rintro z b _ ⟨M, σ, hσ, hσh, hσz, hb, rfl⟩ _ ⟨M', σ', hσ', hσ'h, hσ'z, hb', rfl⟩
    have hiff : σ.val.det = 1 ↔ σ'.val.det = 1 := decide_eq_decide.1 (hb.trans hb'.symm)
    have he : σ.val.det * (σ⁻¹).val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    have hd : σ'.val.det * (σ⁻¹).val.det = 1 := by
      rcases det_eq_one_or_neg_one_of_fix hQ hσ with h1 | h1 <;>
        rcases det_eq_one_or_neg_one_of_fix hQ hσ' with h2 | h2
      · linear_combination he + (σ⁻¹).val.det * h2 - (σ⁻¹).val.det * h1
      · exact absurd (by linear_combination h2 - hiff.1 h1 : (2 : F) = 0) two_ne_zero
      · exact absurd (by linear_combination h1 - hiff.2 h2 : (2 : F) = 0) two_ne_zero
      · linear_combination he + (σ⁻¹).val.det * h2 - (σ⁻¹).val.det * h1
    have hσinv : (σ⁻¹).val *ᵥ h = h := by
      calc (σ⁻¹).val *ᵥ h = (σ⁻¹).val *ᵥ (σ.val *ᵥ h) := by rw [hσh]
        _ = h := by rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have hmem : (σ' * σ⁻¹ : GL (Fin (m + 1)) F) ∈ orthGroup Q F :=
      (orthGroup Q F).mul_mem hσ' ((orthGroup Q F).inv_mem hσ)
    apply Quot.sound
    refine ⟨⟨σ' * σ⁻¹, hmem⟩, ?_, ?_⟩
    · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · change (σ' * σ⁻¹ : GL (Fin (m + 1)) F).val.det = 1
        rw [Units.val_mul, det_mul]; exact hd
      · change (σ' * σ⁻¹ : GL (Fin (m + 1)) F).val *ᵥ h = h
        rw [Units.val_mul, ← mulVec_mulVec, hσinv, hσ'h]
    · apply Lattices.Lat.ext
      change glImage (σ' * σ⁻¹) M.1.1 = M'.1.1
      rw [← hσz, ← hσ'z, ← glImage_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hcov : (Set.univ : Set (hClassesInHGenus Q h L)) ⊆ ⋃ z ∈ Z, ⋃ b : Bool, C z b := by
    intro k _
    induction k using Quot.ind with | mk M => ?_
    obtain ⟨z, hz, σ, hσ, hσh, hσz⟩ := key M
    exact Set.mem_biUnion hz (Set.mem_iUnion.2 ⟨decide (σ.val.det = 1), M, σ, hσ, hσh, hσz, rfl, rfl⟩)
  exact Set.finite_univ_iff.1
    ((hZ.biUnion fun z _ => Set.finite_iUnion fun b => (hsub z b).finite).subset hcov)

/-! ### Step 1: from double cosets to $H$-classes -/

/-- **The map from double cosets to $H$-classes**: $H\eta(H_{\mathbf h}\cap C) \mapsto$ the $H$-class of
$\eta L \in$ the $H$-genus of $L$. -/
def dcToClass {n : ℕ} (Q : QuadForm F n) (h : Fin n → F) (L : Lat F n) :
    hDoubleCosets Q h L → hClassesInHGenus Q h L :=
  Quotient.lift (s := DoubleCoset.setoid _ _)
    (fun η : hAf Q h => (Quot.mk _ ⟨(η : OAf Q) • L, η, η.2, rfl⟩ : hClassesInHGenus Q h L))
    (fun a b hab => by
      have h1 : DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) a = DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) b :=
        Quotient.sound hab
      obtain ⟨ε, hε, hεe⟩ := (dc_mk_eq_iff a b).1 h1
      exact Quot.sound ⟨ε, hε, hεe.symm⟩)

theorem dcToClass_injective {n : ℕ} (Q : QuadForm F n) (h : Fin n → F) (L : Lat F n) :
    Function.Injective (dcToClass Q h L) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | _ a => ?_
  induction y using Quotient.inductionOn with | _ b => ?_
  have h1 := Quot.eqvGen_exact hxy
  rw [Equivalence.eqvGen_iff ((hClassRel_equivalence Q h).comap Subtype.val)] at h1
  obtain ⟨ε, hε, hεe⟩ := h1
  exact (dc_mk_eq_iff a b).2 ⟨ε, hε, hεe.symm⟩

/-- **Reduction**: finiteness of the number of $H$-classes in the $H$-genus of $L$ gives finiteness of
$H\backslash H_{\mathbf h}/(H_{\mathbf h}\cap C)$. -/
theorem finite_hDoubleCosets_of_finite_classes {n : ℕ} (Q : QuadForm F n) (h : Fin n → F) (L : Lat F n)
    (hfin : Finite (hClassesInHGenus Q h L)) : Finite (hDoubleCosets Q h L) :=
  Finite.of_injective _ (dcToClass_injective Q h L)

/-! ### The named input and its consequences -/

/-- **Finiteness of $H\backslash H_{\mathbb A}/(H_{\mathbb A}\cap C)$** (Shimura 2004, Theorem 11.6 (i), p. 104):
the named input `HClassNumberFinite`, for every number field $F$, nondegenerate $\varphi$ with $n > 2$,
lattice $L$ and $h$ with $\varphi[h] \ne 0$. Unconditional. -/
@[kb "shimura2004" "Thm. 11.6 (i), p. 104 (finiteness of H\\H_𝔸/(H_𝔸 ∩ C))"]
theorem hClassNumberFinite : HClassNumberFinite :=
  ⟨fun F _ _ n Q hQ hn L h hh =>
    finite_hDoubleCosets_of_finite_classes Q h L (finite_hClassesInHGenus Q hQ hn L h hh)⟩

/-- **Theorem 11.6 (i) and (11.7)** (Shimura 2004, p. 104), unconditional (Theorem 10.5 is proved). -/
@[kb "shimura2004" "Thm. 11.6 (i) and (11.7), p. 104 (from Theorem 10.5 alone)"]
theorem theorem11_6_i_of_local : Theorem11_6_i :=
  theorem11_6_i_holds hClassNumberFinite

/-- The input `FundamentalTheorem11_6` holds, unconditional (Theorem 10.5 is proved). -/
@[kb "shimura2004" "Thm. 11.6 (i) and (11.7), p. 104 (FundamentalTheorem11_6 from Theorem 10.5 alone)"]
theorem fundamentalTheorem11_6_of_local : FundamentalTheorem11_6 :=
  fundamentalTheorem11_6_holds hClassNumberFinite

end QuadFormsKB.Shimura2004
