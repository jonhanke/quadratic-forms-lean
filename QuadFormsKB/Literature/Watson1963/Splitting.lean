/-
# Watson (1963), §4, Lemma 1: splitting a form of a genus

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549-576.

**Layer:** positive definite integral forms $f$ in $k+m$ variables and $g$ in $k$ variables
(`QuadForm ℤ (k + m)`, `QuadForm ℤ k`, `IntQF.PosDef`); the genus `Siegel.SameGenus`; the orthogonal sum
`QuadForm.orthSum`; lattices in $\mathbb Q^{k+m}$ and their localizations (`Lattices.loc`, `Lattices.LocFamily`).

**Proves** `exists_sameGenus_orthSum` (Watson 1963, Lemma 1, p. 554, the existence of $\psi$; Watson, *Integral Quadratic
Forms*, Theorems 42-43; the gluing of O'Meara 1963, 102:5): if $f \cong g \perp \psi_p$ over $\mathbb Z_p$ for every prime
$p$ (with $\psi_p$ a form over $\mathbb Z_p$ in $m$ variables), then $f$ lies in the genus of $g \perp \psi$ for a
positive definite integral form $\psi$ in $m$ variables.

*Proof.* (1) The first block of the local splittings represents $g$ over every $\mathbb Z_p$, so $g$ is represented over
$\mathbb Q$ by a matrix $X$ (`exists_rat_rep`); let $K = X\mathbb Z^k$ and $C = H_g^{-1}X^{\mathsf T}H_f$, so that
$X(Cx)$ is the projection of $x$ onto $X\mathbb Q^k$ along its orthogonal complement ($H$ denotes the Hessian).
(2) At each place, Witt's theorem (`exists_orthGroup_mulVec_eq`) moves the splitting copy of $g$ to the columns of $X$ by
a local isometry $\sigma$; the lattice $\sigma\mathbb Z_p^{k+m}$ is *good*: it contains the columns of $X$ and the
coordinates $Cy$ of its vectors are integral (`exists_local_good`). At almost all places the standard lattice is good,
because finitely many rational numbers are integral almost everywhere. (3) Gluing these local lattices
(`exists_glued`, as in `exists_sameGenus_le`) gives $M$ in the genus of $\mathbb Z^{k+m}$, containing $K$, with $Cx \in
\mathbb Z^k$ for all $x \in M$, hence $M = K \oplus (M \cap \ker C)$. (4) $M \cap \ker C$ is free ($\mathbb Z$ is a principal ideal domain); with the columns
of $X$ it gives a basis of $M$ adapted to the splitting (`exists_adapted_basis`), whose Gram form is $g \perp \psi$.
The hypothesis is only at the finite primes: positive definiteness takes care of the real place.
-/
import QuadFormsKB.Literature.Watson1963.GenusRep

open Matrix NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel QuadFormsKB

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-! ### Integrality at a place -/

section IntV

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- A vector over $\mathbb Q_v$ is **integral** if all coordinates have valuation at most $1$. -/
def IntV {r : ℕ} (y : Fin r → v.adicCompletion ℚ) : Prop := ∀ i, Valued.v (y i) ≤ 1

variable {v}

theorem intV_mulVec {r s : ℕ} (A : Matrix (Fin r) (Fin s) (v.adicCompletion ℚ))
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) {y : Fin s → v.adicCompletion ℚ} (hy : IntV v y) :
    IntV v (A *ᵥ y) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hA i j) (hy j)

theorem mem_std_iff {r : ℕ} {y : Fin r → v.adicCompletion ℚ} :
    y ∈ (Lattices.std v : Submodule (v.adicCompletionIntegers ℚ) (Fin r → v.adicCompletion ℚ)) ↔
      IntV v y := by
  simp [Lattices.mem_ball, IntV]

end IntV

/-! ### Coefficients of an orthogonal sum -/

section Coeff

variable {A : Type*} [CommRing A] {k m : ℕ}

theorem os_coeff_cc (S : QuadForm A k) (T : QuadForm A m) (a b : Fin k) :
    (QuadForm.orthSum S T).coeff (Fin.castAdd m a) (Fin.castAdd m b) = S.coeff a b := by
  simp only [QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, Fin.addCases_left]
  have h3 : Fin.castAdd m a ≤ Fin.castAdd m b ↔ a ≤ b :=
    Fin.le_iff_val_le_val.trans (Fin.le_iff_val_le_val (a := a) (b := b)).symm
  by_cases h : a ≤ b
  · simp [h3.mpr h]
  · simp [S.upper (show id b < id a from not_le.mp h)]

theorem os_coeff_cn (S : QuadForm A k) (T : QuadForm A m) (a : Fin k) (b : Fin m) :
    (QuadForm.orthSum S T).coeff (Fin.castAdd m a) (Fin.natAdd k b) = 0 := by
  simp only [QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  split_ifs <;> rfl

theorem os_coeff_nc (S : QuadForm A k) (T : QuadForm A m) (a : Fin m) (b : Fin k) :
    (QuadForm.orthSum S T).coeff (Fin.natAdd k a) (Fin.castAdd m b) = 0 := by
  simp only [QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  split_ifs <;> rfl

/-- Rows $0, \dots, k-1$ of the Hessian of $S \perp T$. -/
theorem os_hessian_row (S : QuadForm A k) (T : QuadForm A m) (a : Fin k) (j : Fin (k + m)) :
    (QuadForm.orthSum S T).hessian (Fin.castAdd m a) j =
      Fin.addCases (fun b => S.hessian a b) (fun _ => 0) j := by
  refine Fin.addCases (fun b => ?_) (fun b => ?_) j
  · simp [QuadForm.hessian, os_coeff_cc]
  · simp [QuadForm.hessian, os_coeff_cn, os_coeff_nc]

end Coeff

/-! ### The rational data -/

section Local

variable {k m : ℕ} (f : QuadForm ℤ (k + m)) (g : QuadForm ℤ k)

/-- **The coordinates of the projection onto $K = X\mathbb Q^k$ along $K^\perp$:** for
$X \in \mathbb Q^{(k+m)\times k}$ representing $g$, the projection of $x$ is $X (C x)$ with
$C = H_g^{-1} X^{\mathsf T} H_f$ (the Hessians of $f$, $g$ over $\mathbb Q$). -/
def Cmat (X : Matrix (Fin (k + m)) (Fin k) ℚ) : Matrix (Fin k) (Fin (k + m)) ℚ :=
  (g.map (Int.castRingHom ℚ)).hessian⁻¹ * (Xᵀ * (f.map (Int.castRingHom ℚ)).hessian)

variable {f g}

theorem xhx {X : Matrix (Fin (k + m)) (Fin k) ℚ} (hX : ∀ y, f.evalIn ℚ (X *ᵥ y) = g.evalIn ℚ y) :
    Xᵀ * (f.map (Int.castRingHom ℚ)).hessian * X = (g.map (Int.castRingHom ℚ)).hessian := by
  have h1 : (f.map (Int.castRingHom ℚ)).compMat X = g.map (Int.castRingHom ℚ) :=
    QuadForm.eq_of_eval_eq fun y => by
      rw [QuadForm.eval_compMat]
      exact (evalIn_rat_eq f _).trans ((hX y).trans (evalIn_rat_eq g y).symm)
  have := congrArg QuadForm.hessian h1
  rwa [QuadForm.hessian_compMat] at this

theorem hg_cmat (hg : IntQF.PosDef g) (X : Matrix (Fin (k + m)) (Fin k) ℚ) :
    (g.map (Int.castRingHom ℚ)).hessian * Cmat f g X = Xᵀ * (f.map (Int.castRingHom ℚ)).hessian := by
  have hd : IsUnit (g.map (Int.castRingHom ℚ)).hessian.det :=
    isUnit_iff_ne_zero.mpr (isTotallyPosDef_map_rat hg).nondegenerate
  exact Matrix.mul_nonsing_inv_cancel_left _ _ hd

variable (f g)

/-- **The local goodness condition** for a lattice $N \subseteq \mathbb Q_v^{k+m}$: it contains the columns of $X$,
and the projection coordinates $C y$ of each $y \in N$ are integral. -/
def Good (X : Matrix (Fin (k + m)) (Fin k) ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (N : Submodule (v.adicCompletionIntegers ℚ) (Fin (k + m) → v.adicCompletion ℚ)) : Prop :=
  (∀ j, Lattices.locVec v (fun i => X i j) ∈ N) ∧
    ∀ y ∈ N, IntV v ((Cmat f g X).map (algebraMap ℚ (v.adicCompletion ℚ)) *ᵥ y)

variable {f g}

/-- **The first $k$ columns of a splitting matrix represent $g$:** if $f(T\vec x) = (g \perp \psi)(\vec x)$ over a
commutative ring $S$, then $f(H\vec a) = g(\vec a)$ for $H$ the first $k$ columns of $T$. -/
theorem eval_firstCols {S : Type*} [CommRing S] {T : GL (Fin (k + m)) S} {ψp : QuadForm S m}
    (hT : ∀ x, (f.map (Int.castRingHom S)).eval (T.val *ᵥ x) =
      (QuadForm.orthSum (g.map (Int.castRingHom S)) ψp).eval x) (a : Fin k → S) :
    f.evalIn S ((fun i (b : Fin k) => T.val i (Fin.castAdd m b)) *ᵥ a) = g.evalIn S a := by
  let x : Fin (k + m) → S := Fin.addCases a (fun _ => 0)
  have e : (fun i (b : Fin k) => T.val i (Fin.castAdd m b)) *ᵥ a = T.val *ᵥ x := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, x]
  have h1 := hT x
  have h2 := QuadForm.evalIn_orthSum S (g.map (Int.castRingHom S)) ψp x
  rw [e, evalIn_int_eq_eval_map]
  refine h1.trans (h2.trans ?_)
  have h3 : ψp.evalIn S (fun b => x (Fin.natAdd k b)) = 0 := by
    simp [x, QuadForm.evalIn]
  rw [h3, add_zero, evalIn_int_eq_eval_map]
  simp [x]

/-- **Local splitting** (the local step of Watson 1963, Lemma 1): if $f \cong g \perp \psi_p$ over $\mathbb Z_p$,
some local isometry $\sigma$ of $f$ carries $\mathbb Z_p^{k+m}$ to a lattice that is good for $X$. -/
theorem exists_local_good (hf : IntQF.PosDef f) (hg : IntQF.PosDef g)
    {X : Matrix (Fin (k + m)) (Fin k) ℚ} (hX : ∀ y, f.evalIn ℚ (X *ᵥ y) = g.evalIn ℚ y)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ ψp : QuadForm ℤ_[p] m,
      IsometricGL (f.map (Int.castRingHom ℤ_[p])) (QuadForm.orthSum (g.map (Int.castRingHom ℤ_[p])) ψp)) :
    ∃ σ ∈ Lattices.orthGroup (f.map (Int.castRingHom ℚ)) (v.adicCompletion ℚ),
      Good f g X v (Lattices.locAct v σ (Lattices.loc v Lattices.intVec)) := by
  classical
  obtain ⟨p, hp, ψ, hψ⟩ := exists_padic_hom v
  obtain ⟨ψp, T, hT⟩ := hloc p
  have hQnd := (isTotallyPosDef_map_rat hf).nondegenerate
  have hTnd := (isTotallyPosDef_map_rat hg).nondegenerate
  have hψv : ∀ x, Valued.v (ψ x) ≤ 1 := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hψ x)
  let H1 : Matrix (Fin (k + m)) (Fin k) ℤ_[p] := fun i b => T.val i (Fin.castAdd m b)
  let T' : Matrix (Fin (k + m)) (Fin (k + m)) (v.adicCompletion ℚ) := T.val.map ψ
  let Y : Matrix (Fin (k + m)) (Fin k) (v.adicCompletion ℚ) := H1.map ψ
  have hH1 : ∀ a : Fin k → ℤ_[p], f.evalIn ℤ_[p] (H1 *ᵥ a) = g.evalIn ℤ_[p] a := eval_firstCols hT
  -- the Hessian relation
  have hcomp : (f.map (Int.castRingHom ℤ_[p])).compMat T.val =
      QuadForm.orthSum (g.map (Int.castRingHom ℤ_[p])) ψp :=
    QuadForm.eq_of_eval_eq fun x => by rw [QuadForm.eval_compMat]; exact hT x
  have hS := congrArg QuadForm.hessian hcomp
  rw [QuadForm.hessian_compMat] at hS
  set Hv : Matrix (Fin (k + m)) (Fin (k + m)) (v.adicCompletion ℚ) :=
    (f.map (Int.castRingHom ℚ)).hessian.map (algebraMap ℚ (v.adicCompletion ℚ)) with hHv
  set Hgv : Matrix (Fin k) (Fin k) (v.adicCompletion ℚ) :=
    (g.map (Int.castRingHom ℚ)).hessian.map (algebraMap ℚ (v.adicCompletion ℚ)) with hHgv
  have hHv' : (f.map (Int.castRingHom ℤ_[p])).hessian.map ψ = Hv := by
    ext i j; simp [Hv, QuadForm.hessian, QuadForm.map]
  have hg' : ∀ a b, ψ ((g.map (Int.castRingHom ℤ_[p])).hessian a b) = Hgv a b := fun a b => by
    simp [Hgv, QuadForm.hessian, QuadForm.map]
  have hS' : T'ᵀ * Hv * T' = (QuadForm.orthSum (g.map (Int.castRingHom ℤ_[p])) ψp).hessian.map ψ := by
    have := congrArg (fun M => M.map ψ) hS
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [hHv'] at this
    exact this
  have hrow : ∀ (a : Fin k) (j : Fin (k + m)), (T'ᵀ * Hv * T') (Fin.castAdd m a) j =
      Fin.addCases (fun b => Hgv a b) (fun _ => 0) j := by
    intro a j
    rw [hS', Matrix.map_apply, os_hessian_row]
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · simp [hg']
    · simp
  -- the representations
  have hY : ∀ y, (f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Y *ᵥ y) =
      (g.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y := fun y => by
    rw [evalIn_rat_eq, evalIn_rat_eq]; exact evalIn_map_mulVec ψ hH1 y
  have hX' : ∀ y, (f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ)
      (X.map (algebraMap ℚ (v.adicCompletion ℚ)) *ᵥ y) =
      (g.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y := fun y => by
    rw [evalIn_rat_eq, evalIn_rat_eq]
    exact evalIn_map_mulVec (algebraMap ℚ (v.adicCompletion ℚ)) (fun y => by
      rw [← evalIn_rat_eq, ← evalIn_rat_eq]; exact hX y) y
  obtain ⟨σ, hσ, hσY⟩ := exists_orthGroup_mulVec_eq (f.map (Int.castRingHom ℚ)) hQnd
    (g.map (Int.castRingHom ℚ)) hTnd _ _ hX' hY
  have hσmat : σ.val * Y = X.map (algebraMap ℚ (v.adicCompletion ℚ)) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hσY (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    exact this
  refine ⟨σ, hσ, ?_⟩
  unfold Good
  refine ⟨fun j => ?_, fun y hy => ?_⟩
  · have h1 : Lattices.locVec v (fun i => X i j) =
        σ.val *ᵥ (Y *ᵥ Pi.single j 1) := by
      rw [Matrix.mulVec_mulVec, hσmat, Matrix.mulVec_single_one]; rfl
    rw [h1]
    refine ⟨Y *ᵥ Pi.single j 1, ?_, rfl⟩
    change _ ∈ Lattices.loc v Lattices.intVec
    rw [Lattices.loc_intVec, mem_std_iff]
    intro i
    rw [Matrix.mulVec_single_one]
    exact hψv _
  · obtain ⟨z, hz, rfl⟩ := Lattices.mem_locAct.mp hy
    rw [Lattices.loc_intVec, mem_std_iff] at hz
    let w : Fin (k + m) → v.adicCompletion ℚ := (T⁻¹.val.map ψ) *ᵥ z
    have hw : IntV v w := intV_mulVec _ (fun i j => hψv _) hz
    have hzw : T' *ᵥ w = z := by
      simp only [w, T', Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel]
      simp
    have hHgi : Function.Injective Hgv.mulVec := by
      have hdet : Hgv.det ≠ 0 := by
        rw [hHgv, show ((g.map (Int.castRingHom ℚ)).hessian.map (algebraMap ℚ (v.adicCompletion ℚ))).det =
          algebraMap ℚ (v.adicCompletion ℚ) (g.map (Int.castRingHom ℚ)).hessian.det from
          (RingHom.map_det _ _).symm]
        exact (map_ne_zero_iff _ (algebraMap ℚ _).injective).mpr hTnd
      intro a b hab
      have : Hgv *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
      exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hdet this)
    have key : (Cmat f g X).map (algebraMap ℚ (v.adicCompletion ℚ)) *ᵥ (σ.val *ᵥ z) =
        fun i => w (Fin.castAdd m i) := by
      apply hHgi
      have hC : Hgv * (Cmat f g X).map (algebraMap ℚ (v.adicCompletion ℚ)) =
          (X.map (algebraMap ℚ (v.adicCompletion ℚ)))ᵀ * Hv := by
        have := congrArg (fun M => M.map (algebraMap ℚ (v.adicCompletion ℚ))) (hg_cmat (f := f) hg X)
        simpa [Matrix.map_mul, Matrix.transpose_map] using this
      have hσo : σ.valᵀ * Hv * σ.val = Hv := (Lattices.mem_orthGroup _).mp hσ
      show Hgv *ᵥ _ = Hgv *ᵥ _
      rw [Matrix.mulVec_mulVec, hC, Matrix.mulVec_mulVec, ← hσmat, Matrix.transpose_mul]
      have e1 : (Yᵀ * σ.valᵀ * Hv) * σ.val = Yᵀ * Hv := by
        calc (Yᵀ * σ.valᵀ * Hv) * σ.val = Yᵀ * (σ.valᵀ * Hv * σ.val) := by simp only [Matrix.mul_assoc]
          _ = Yᵀ * Hv := by rw [hσo]
      rw [e1, ← hzw, Matrix.mulVec_mulVec]
      have hrow2 : ∀ (a : Fin k) (j : Fin (k + m)), (Yᵀ * Hv * T') a j =
          Fin.addCases (fun b => Hgv a b) (fun _ => 0) j := fun a j => hrow a j
      funext i
      simp only [Matrix.mulVec, dotProduct, hrow2, Fin.sum_univ_add, Fin.addCases_left,
        Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
    rw [key]
    intro i; exact hw _

/-- **The glued lattice** (Watson 1963, Lemma 1, local-to-global step; O'Meara 102:5 in the form of
`exists_sameGenus_le`): there is a lattice $M$ in the genus of $\mathbb Z^{k+m}$ in $(\mathbb Q^{k+m}, f)$ that contains the
columns of $X$ and such that the projection coordinates $C x$ of every $x \in M$ are integers. -/
theorem exists_glued (hf : IntQF.PosDef f) (hg : IntQF.PosDef g)
    {X : Matrix (Fin (k + m)) (Fin k) ℚ} (hX : ∀ y, f.evalIn ℚ (X *ᵥ y) = g.evalIn ℚ y)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ ψp : QuadForm ℤ_[p] m,
      IsometricGL (f.map (Int.castRingHom ℤ_[p])) (QuadForm.orthSum (g.map (Int.castRingHom ℤ_[p])) ψp)) :
    ∃ M : Submodule (𝓞 ℚ) (Fin (k + m) → ℚ), M.IsLattice ℚ ∧
      Lattices.SameGenus (f.map (Int.castRingHom ℚ)) Lattices.intVec M ∧
      (∀ j, (fun i => X i j) ∈ M) ∧
      ∀ x ∈ M, ∃ z : Fin k → 𝓞 ℚ, Cmat f g X *ᵥ x = Lattices.intCoe z := by
  classical
  choose σ hσ hgood using fun v => exists_local_good hf hg hX v hloc
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      Good f g X v (Lattices.loc v Lattices.intVec) := by
    have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
        ∀ (i : Fin (k + m)) (j : Fin k), v.valuation ℚ (X i j) ≤ 1 :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        Lattices.eventually_valuation_le_one _
    have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
        ∀ (i : Fin k) (j : Fin (k + m)), v.valuation ℚ (Cmat f g X i j) ≤ 1 :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        Lattices.eventually_valuation_le_one _
    filter_upwards [h1, h2] with v h1 h2
    rw [Lattices.loc_intVec]
    refine ⟨fun j => ?_, fun y hy => ?_⟩
    · rw [mem_std_iff]
      intro i
      simp only [Lattices.locVec_apply, Lattices.valued_algebraMap]
      exact h1 i j
    · rw [mem_std_iff] at hy
      refine intV_mulVec _ (fun i j => ?_) hy
      simp only [Matrix.map_apply, Lattices.valued_algebraMap]
      exact h2 i j
  let M : Lattices.LocFamily ℚ (k + m) :=
    { M := fun v => if Good f g X v (Lattices.loc v Lattices.intVec) then Lattices.loc v Lattices.intVec
        else Lattices.locAct v (σ v) (Lattices.loc v Lattices.intVec)
      isLattice := fun v => by
        split_ifs
        · exact Lattices.loc_isLattice v Lattices.intVec_isLattice
        · exact Lattices.locAct_isLattice _ (Lattices.loc_isLattice v Lattices.intVec_isLattice)
      eventually_std := by
        filter_upwards [hev] with v hv
        simp only [hv, ↓reduceIte]; rw [Lattices.loc_intVec] }
  have hM : ∀ v, Good f g X v (M.M v) := fun v => by
    change Good f g X v (if _ then _ else _)
    split_ifs with h
    · exact h
    · exact hgood v
  refine ⟨M.glue, M.glue_isLattice, fun v => ?_, fun j => ?_, fun x hx => ?_⟩
  · change ∃ g' ∈ Lattices.orthGroup (f.map (Int.castRingHom ℚ)) _,
      Lattices.locAct v g' (Lattices.loc v Lattices.intVec) = Lattices.loc v M.glue
    rw [M.loc_glue]
    change ∃ g' ∈ Lattices.orthGroup (f.map (Int.castRingHom ℚ)) _,
      Lattices.locAct v g' (Lattices.loc v Lattices.intVec) =
        if Good f g X v (Lattices.loc v Lattices.intVec) then Lattices.loc v Lattices.intVec
        else Lattices.locAct v (σ v) (Lattices.loc v Lattices.intVec)
    split_ifs
    · exact ⟨1, (Lattices.orthGroup (f.map (Int.castRingHom ℚ)) _).one_mem, Lattices.locAct_one _⟩
    · exact ⟨σ v, hσ v, rfl⟩
  · exact fun w => (hM w).1 j
  · have hmem : Cmat f g X *ᵥ x ∈ (Lattices.intVec : Submodule (𝓞 ℚ) (Fin k → ℚ)) := by
      rw [Lattices.mem_intVec_iff_valuation]
      intro w i
      have h1 := (hM w).2 _ (Lattices.LocFamily.mem_glue.mp hx w)
      have h2 : (Cmat f g X).map (algebraMap ℚ (w.adicCompletion ℚ)) *ᵥ Lattices.locVec w x =
          fun i => algebraMap ℚ (w.adicCompletion ℚ) ((Cmat f g X *ᵥ x) i) := by
        funext i
        exact (RingHom.map_mulVec (algebraMap ℚ (w.adicCompletion ℚ)) (Cmat f g X) x i).symm
      rw [h2] at h1
      have := h1 i
      rwa [Lattices.valued_algebraMap] at this
    obtain ⟨z, hz⟩ := Lattices.mem_intVec_iff_exists.mp hmem
    exact ⟨z, hz.symm⟩

theorem cmat_X (hg : IntQF.PosDef g) {X : Matrix (Fin (k + m)) (Fin k) ℚ}
    (hXHX : Xᵀ * (f.map (Int.castRingHom ℚ)).hessian * X = (g.map (Int.castRingHom ℚ)).hessian) :
    Cmat f g X * X = 1 := by
  have hd : IsUnit (g.map (Int.castRingHom ℚ)).hessian.det :=
    isUnit_iff_ne_zero.mpr (isTotallyPosDef_map_rat hg).nondegenerate
  have h := hg_cmat (f := f) hg X
  have h2 : (g.map (Int.castRingHom ℚ)).hessian * (Cmat f g X * X) =
      (g.map (Int.castRingHom ℚ)).hessian := by
    rw [← Matrix.mul_assoc, h, hXHX]
  have h3 := congrArg (fun A => (g.map (Int.castRingHom ℚ)).hessian⁻¹ * A) h2
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul] at h3
  exact h3

/-- **An adapted basis of the glued lattice:** $M = \gamma \mathcal O^{k+m}$ where the first $k$ columns of $\gamma$
are the columns of $X$ and the last $m$ columns lie in the kernel of the projection coordinates $C$ (that is, in
$K^\perp$). Proof: $M \cap \ker C$ is a free module ($\mathbb Z$ is a principal ideal domain); together with the columns of $X$ it is a $\mathbb Q$-basis
(so there are exactly $m$ further columns) and generates $M$. -/
theorem exists_adapted_basis (hg : IntQF.PosDef g) {X : Matrix (Fin (k + m)) (Fin k) ℚ}
    (hXHX : Xᵀ * (f.map (Int.castRingHom ℚ)).hessian * X = (g.map (Int.castRingHom ℚ)).hessian)
    {M : Submodule (𝓞 ℚ) (Fin (k + m) → ℚ)} (hM : M.IsLattice ℚ)
    (hcols : ∀ j, (fun i => X i j) ∈ M)
    (hcoord : ∀ x ∈ M, ∃ z : Fin k → 𝓞 ℚ, Cmat f g X *ᵥ x = Lattices.intCoe z) :
    ∃ γ : GL (Fin (k + m)) ℚ, Lattices.latOf γ = M ∧
      (∀ (j : Fin k) (i : Fin (k + m)), γ.val i (Fin.castAdd m j) = X i j) ∧
      ∀ i : Fin m, Cmat f g X *ᵥ (fun r => γ.val r (Fin.natAdd k i)) = 0 := by
  classical
  set Cm := Cmat f g X with hCm
  have hCX : Cm * X = 1 := cmat_X hg hXHX
  have hXc : ∀ c : Fin k → ℚ, X *ᵥ c = ∑ j, c j • (fun r => X r j) := by
    intro c; funext r; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hXz : ∀ z : Fin k → 𝓞 ℚ, X *ᵥ Lattices.intCoe z = ∑ j, z j • (fun r => X r j) := by
    intro z
    rw [hXc]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (algebraMap_smul ℚ (z j) _).symm
  have hFin : Module.Finite (𝓞 ℚ) M := Module.Finite.iff_fg.mpr hM.fg
  obtain ⟨Mp, hMp⟩ : ∃ Mp : Submodule (𝓞 ℚ) (Fin (k + m) → ℚ),
      ∀ x, x ∈ Mp ↔ x ∈ M ∧ Cm *ᵥ x = 0 :=
    ⟨M ⊓ (LinearMap.ker (Matrix.mulVecLin Cm)).restrictScalars (𝓞 ℚ), fun x => by simp⟩
  have hMpM : Mp ≤ M := fun x hx => ((hMp x).mp hx).1
  have hNoeth : IsNoetherian (𝓞 ℚ) M := inferInstance
  have hFinMp : Module.Finite (𝓞 ℚ) Mp :=
    Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hMpM)
  have hFreeMp : Module.Free (𝓞 ℚ) Mp := Module.free_of_finite_type_torsion_free' (R := 𝓞 ℚ) (M := Mp)
  obtain ⟨ι, hιFin, ⟨b⟩⟩ : ∃ ι : Type, Finite ι ∧ Nonempty (Module.Basis ι (𝓞 ℚ) Mp) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis (𝓞 ℚ) Mp⟩⟩
  have hιF : Fintype ι := Fintype.ofFinite ι
  let bv : ι → (Fin (k + m) → ℚ) := fun i => (b i : Fin (k + m) → ℚ)
  have hbvM : ∀ i, bv i ∈ M := fun i => hMpM (b i).2
  have hbvC : ∀ i, Cm *ᵥ bv i = 0 := fun i => ((hMp _).mp (b i).2).2
  have hbli : LinearIndependent ℚ bv := by
    have h1 := b.linearIndependent.map' Mp.subtype (Submodule.ker_subtype _)
    exact (LinearIndependent.iff_fractionRing (𝓞 ℚ) ℚ).mp h1
  have hbspan : ∀ x ∈ M, Cm *ᵥ x = 0 → ∃ r : ι → 𝓞 ℚ, x = ∑ i, r i • bv i := by
    intro x hx h0
    let x' : Mp := ⟨x, (hMp x).mpr ⟨hx, h0⟩⟩
    refine ⟨fun i => b.repr x' i, ?_⟩
    have := congrArg Subtype.val (b.sum_repr x')
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  let u : Fin k ⊕ ι → (Fin (k + m) → ℚ) := Sum.elim (fun j r => X r j) bv
  have hu_mem : ∀ c, u c ∈ M := by
    rintro (j | i)
    · exact hcols j
    · exact hbvM i
  have hli : LinearIndependent ℚ u := by
    rw [Fintype.linearIndependent_iff]
    intro g' hg'
    rw [Fintype.sum_sum_type] at hg'
    simp only [u, Sum.elim_inl, Sum.elim_inr] at hg'
    have hsum : Cm *ᵥ (∑ i, g' (Sum.inr i) • bv i) = 0 := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Matrix.mulVec_smul, hbvC, smul_zero]
    have h1 := congrArg (fun y => Cm *ᵥ y) hg'
    simp only [Matrix.mulVec_add, hsum, add_zero, Matrix.mulVec_zero] at h1
    rw [← hXc (fun j => g' (Sum.inl j)), Matrix.mulVec_mulVec, hCX, Matrix.one_mulVec] at h1
    have hg1 : ∀ j, g' (Sum.inl j) = 0 := fun j => congrFun h1 j
    simp only [hg1, zero_smul, Finset.sum_const_zero, zero_add] at hg'
    have hg2 := Fintype.linearIndependent_iff.mp hbli (fun i => g' (Sum.inr i)) hg'
    rintro (j | i)
    · exact hg1 j
    · exact hg2 i
  have hspanR : ∀ x ∈ M, x ∈ Submodule.span (𝓞 ℚ) (Set.range u) := by
    intro x hx
    obtain ⟨z, hz⟩ := hcoord x hx
    have hXzM : X *ᵥ Lattices.intCoe z ∈ M := by
      rw [hXz]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcols j)
    have hXzS : X *ᵥ Lattices.intCoe z ∈ Submodule.span (𝓞 ℚ) (Set.range u) := by
      rw [hXz]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    have hw0 : Cm *ᵥ (x - X *ᵥ Lattices.intCoe z) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hCX, Matrix.one_mulVec, hz, sub_self]
    obtain ⟨r, hr⟩ := hbspan _ (M.sub_mem hx hXzM) hw0
    have : x = X *ᵥ Lattices.intCoe z + ∑ i, r i • bv i := by rw [← hr]; abel
    rw [this]
    refine Submodule.add_mem _ hXzS (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range u) := by
    rw [← hM.span_eq_top]
    refine Submodule.span_le.mpr fun x hx => ?_
    exact Submodule.span_le_restrictScalars (𝓞 ℚ) ℚ _ (hspanR x hx)
  set bF := Module.Basis.mk hli hspan
  have hcard : Fintype.card (Fin k ⊕ ι) = k + m := by
    rw [← Module.finrank_eq_card_basis bF]; simp
  have hcardι : Fintype.card ι = m := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard; omega
  set e : ι ≃ Fin m := Fintype.equivFinOfCardEq hcardι
  set E : Fin (k + m) ≃ Fin k ⊕ ι :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) e.symm) with hE
  have hEl : ∀ j : Fin k, E (Fin.castAdd m j) = Sum.inl j := fun j => by
    simp [E, finSumFinEquiv_symm_apply_castAdd]
  have hEr : ∀ i : Fin m, E (Fin.natAdd k i) = Sum.inr (e.symm i) := fun i => by
    simp [E, finSumFinEquiv_symm_apply_natAdd]
  set γM : Matrix (Fin (k + m)) (Fin (k + m)) ℚ := Matrix.of fun r c => u (E c) r
  have hcol : ∀ c, γM.col c = u (E c) := fun c => by ext i; rfl
  have hunit : IsUnit γM := by
    refine Matrix.linearIndependent_col_iff_isUnit.mp ?_
    have : γM.col = u ∘ E := funext hcol
    rw [this]
    exact hli.comp _ E.injective
  refine ⟨hunit.unit, ?_, fun j i => ?_, fun i => ?_⟩
  · have hmul : ∀ y : Fin (k + m) → ℚ, hunit.unit.val *ᵥ y = ∑ j, y j • u (E j) := by
      intro y
      rw [← Lattices.sum_smul_col]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [IsUnit.unit_spec, Matrix.mulVec_single_one]
      exact hcol j
    ext x
    rw [Lattices.latOf, Lattices.mem_glImage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := Lattices.mem_intVec_iff_exists.mp hy
      rw [hmul]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [show (Lattices.intCoe a j) • u (E j) = a j • u (E j) from algebraMap_smul ℚ (a j) (u (E j))]
      exact Submodule.smul_mem _ _ (hu_mem _)
    · intro hx
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp (hspanR x hx)
      refine ⟨fun j => algebraMap (𝓞 ℚ) ℚ (c (E j)), Lattices.intCoe_mem _, ?_⟩
      rw [hmul, Finsupp.sum_fintype c (fun i a => a • u i) (fun i => zero_smul _ _)]
      rw [← E.sum_comp]
      exact Finset.sum_congr rfl fun j _ => algebraMap_smul ℚ (c (E j)) (u (E j))
  · show γM i (Fin.castAdd m j) = X i j
    simp [γM, hEl, u]
  · have : (fun r => hunit.unit.val r (Fin.natAdd k i)) = bv (e.symm i) := by
      funext r
      show γM r (Fin.natAdd k i) = _
      simp [γM, hEr, u]
    rw [this]
    exact hbvC _

/-! ### The theorem -/

/-- **Splitting in the genus** (Watson 1963, Lemma 1, p. 554, the existence of $\psi$; Watson, *Integral Quadratic Forms*,
Theorems 42-43; O'Meara 1963, 102:5 and gluing). Let $f$ be a positive definite integral form in $k + m$ variables and
$g$ a positive definite integral form in $k$ variables. If for every prime $p$ the form $f$ is $\mathrm{GL}$-equivalent over
$\mathbb Z_p$ to $g \perp \psi_p$ for some form $\psi_p$ over $\mathbb Z_p$ in $m$ variables (`hloc`), then there is a
positive definite integral form $\psi$ in $m$ variables such that $f$ lies in the genus of $g \perp \psi$
(`Siegel.SameGenus f (QuadForm.orthSum g ψ)`). Arguments: `hf`, `hg` (positive definiteness) and `hloc`.

*Proof.* The first block of `hloc` says that $f$ represents $g$ over every $\mathbb Z_p$, so over $\mathbb Q$ by a matrix $X$
(`exists_rat_rep`). Locally Witt's theorem moves the splitting copy of $g$ onto the columns of $X$ (`exists_local_good`);
gluing (`exists_glued`) gives a lattice $M$ in the genus of $\mathbb Z^{k+m}$ that is the orthogonal sum of $X\mathbb Z^k$ and
$M \cap (X\mathbb Q^k)^\perp$; a basis adapted to this splitting (`exists_adapted_basis`) gives the form $g \perp \psi$. -/
@[kb "watson1963" "§4, Lemma 1, p. 554 (existence of ψ; local splitting gives a splitting in the genus)"]
theorem exists_sameGenus_orthSum {k m : ℕ} {f : QuadForm ℤ (k + m)} {g : QuadForm ℤ k}
    (hf : IntQF.PosDef f) (hg : IntQF.PosDef g)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ ψp : QuadForm ℤ_[p] m,
      IsometricGL (f.map (Int.castRingHom ℤ_[p])) (QuadForm.orthSum (g.map (Int.castRingHom ℤ_[p])) ψp)) :
    ∃ ψ : QuadForm ℤ m, IntQF.PosDef ψ ∧ Siegel.SameGenus f (QuadForm.orthSum g ψ) := by
  classical
  have hRep : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] f g := fun p _ => by
    obtain ⟨ψp, T, hT⟩ := hloc p
    exact ⟨fun i (b : Fin k) => T.val i (Fin.castAdd m b), eval_firstCols hT⟩
  obtain ⟨X, hX⟩ := exists_rat_rep hf hg hRep
  obtain ⟨M, hMlat, hMg, hcols, hcoord⟩ := exists_glued hf hg hX hloc
  obtain ⟨γ, hγ, hγX, hγC⟩ := exists_adapted_basis hg (xhx hX) hMlat hcols hcoord
  have hM' : Lattices.SameGenus (HilbertModular.formF (Tamagawa.RatBridge.up f)) Lattices.intVec
      (Lattices.latOf γ) := by
    rw [Tamagawa.RatBridge.formF_up, hγ]; exact hMg
  have hi : Lattices.IsIntegral (HilbertModular.formF (Tamagawa.RatBridge.up f)) (Lattices.latOf γ) :=
    Lattices.SameGenus.isIntegral _ (HilbertModular.isIntegral_stdLat (Tamagawa.RatBridge.up f)) hM'
  set f' := Tamagawa.RatBridge.down (Lattices.gramZ (HilbertModular.formF (Tamagawa.RatBridge.up f)) γ hi)
    with hf'
  have hs : Siegel.SameGenus f f' := Tamagawa.RatBridge.sameGenus_down_gramZ f γ hM' hi
  -- the value of f'
  have hval : ∀ y : Fin (k + m) → ℤ, ((f'.eval y : ℤ) : ℚ) =
      f.evalIn ℚ (γ.val *ᵥ (fun i => (y i : ℚ))) := by
    intro y
    have e1 : y = fun i => Tamagawa.RatBridge.eZ (Tamagawa.RatBridge.eZ.symm (y i)) := by
      funext i; simp
    conv_lhs => rw [hf', e1]
    rw [Tamagawa.RatBridge.down_map_eval, Lattices.eZ_cast_eq, Lattices.algebraMap_eval_gramZ,
      Tamagawa.RatBridge.formF_up]
    have e2 : Lattices.intCoe (fun i => Tamagawa.RatBridge.eZ.symm (y i)) = fun i => (y i : ℚ) := by
      funext i
      simp
    rw [e2]
    exact evalIn_rat_eq f _
  -- the columns of γ
  let Wm : Matrix (Fin (k + m)) (Fin m) ℚ := fun r i => γ.val r (Fin.natAdd k i)
  have hsplit : ∀ y : Fin (k + m) → ℚ, γ.val *ᵥ y =
      X *ᵥ (fun a => y (Fin.castAdd m a)) + Wm *ᵥ (fun b => y (Fin.natAdd k b)) := by
    intro y
    funext r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Pi.add_apply, hγX, Wm]
  have hCW : Cmat f g X * Wm = 0 := by
    refine Matrix.ext fun r i => ?_
    have := congrFun (hγC i) r
    show ∑ x, Cmat f g X r x * Wm x i = (0 : Matrix (Fin k) (Fin m) ℚ) r i
    simpa [Matrix.mulVec, dotProduct, Wm] using this
  have hortho : ∀ (a : Fin k → ℚ) (b : Fin m → ℚ),
      (X *ᵥ a) ⬝ᵥ ((f.map (Int.castRingHom ℚ)).hessian *ᵥ (Wm *ᵥ b)) = 0 := by
    intro a b
    have h1 : Xᵀ *ᵥ ((f.map (Int.castRingHom ℚ)).hessian *ᵥ (Wm *ᵥ b)) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hg_cmat (f := f) hg X, Matrix.mul_assoc, hCW,
        Matrix.mul_zero, Matrix.zero_mulVec]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h1, zero_dotProduct]
  have hwval : ∀ (a : Fin k → ℚ) (b : Fin m → ℚ),
      f.evalIn ℚ (X *ᵥ a + Wm *ᵥ b) = g.evalIn ℚ a + f.evalIn ℚ (Wm *ᵥ b) := by
    intro a b
    have h := QuadForm.polar_eq_hessian ℚ (f.map (Int.castRingHom ℚ)) (X *ᵥ a) (Wm *ᵥ b)
    have h' : (f.map (Int.castRingHom ℚ)).hessian.map (algebraMap ℚ ℚ) =
        (f.map (Int.castRingHom ℚ)).hessian := by ext; simp
    rw [h', hortho, evalIn_rat_eq, evalIn_rat_eq, evalIn_rat_eq] at h
    have hXa : f.evalIn ℚ (X *ᵥ a) = g.evalIn ℚ a := hX a
    linarith
  have hval2 : ∀ y : Fin (k + m) → ℤ, ((f'.eval y : ℤ) : ℚ) =
      g.evalIn ℚ (fun a => (y (Fin.castAdd m a) : ℚ)) +
        f.evalIn ℚ (Wm *ᵥ (fun b => (y (Fin.natAdd k b) : ℚ))) := fun y => by
    rw [hval, hsplit]
    exact hwval _ _
  -- the sublattice form
  let E : Matrix (Fin (k + m)) (Fin m) ℤ := fun i j => if i = Fin.natAdd k j then 1 else 0
  have hEc : ∀ (b : Fin m → ℤ) (a : Fin k), (E *ᵥ b) (Fin.castAdd m a) = 0 := fun b a => by
    simp only [Matrix.mulVec, dotProduct, E]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : Fin.castAdd m a ≠ Fin.natAdd k j := fun h => by
      have := congrArg Fin.val h
      simp at this; omega
    simp [this]
  have hEn : ∀ (b : Fin m → ℤ) (j : Fin m), (E *ᵥ b) (Fin.natAdd k j) = b j := fun b j => by
    simp [Matrix.mulVec, dotProduct, E]
  set ψ := f'.compMat E with hψ
  have hψeval : ∀ b : Fin m → ℤ, ((ψ.eval b : ℤ) : ℚ) = f.evalIn ℚ (Wm *ᵥ (fun j => (b j : ℚ))) := by
    intro b
    rw [hψ, QuadForm.eval_compMat, hval2]
    have h0 : (fun a => (((E *ᵥ b) (Fin.castAdd m a) : ℤ) : ℚ)) = 0 := by
      funext a; simp [hEc]
    have h1 : (fun j => (((E *ᵥ b) (Fin.natAdd k j) : ℤ) : ℚ)) = fun j => (b j : ℚ) := by
      funext j; simp [hEn]
    rw [h0, h1]
    simp [QuadForm.evalIn]
  have hfin : ∀ y : Fin (k + m) → ℤ, f'.eval y =
      g.eval (fun a => y (Fin.castAdd m a)) + ψ.eval (fun b => y (Fin.natAdd k b)) := by
    intro y
    apply Int.cast_injective (α := ℚ)
    rw [hval2, Int.cast_add, hψeval]
    congr 1
    exact Siegel.evalIn_intCast (K := ℚ) g _
  refine ⟨ψ, ?_, ?_⟩
  · intro b hb
    have hpos : ∀ w : Fin (k + m) → ℚ, w ≠ 0 → 0 < f.evalIn ℚ w := by
      intro w hw
      have h := hf.evalIn_real_pos (fun i => (w i : ℝ)) (by
        intro h0; apply hw; funext i; have := congrFun h0 i; simpa using this)
      have e := AWS.evalIn_map f (Rat.castHom ℝ) w
      have h2 : (0 : ℝ) < ((f.evalIn ℚ w : ℚ) : ℝ) := by
        rw [show ((f.evalIn ℚ w : ℚ) : ℝ) = Rat.castHom ℝ (f.evalIn ℚ w) from rfl, e]; exact h
      exact_mod_cast h2
    have hw : Wm *ᵥ (fun j => (b j : ℚ)) ≠ 0 := by
      intro h0
      have h3 : γ.val *ᵥ (fun i => (((E *ᵥ b) i : ℤ) : ℚ)) = 0 := by
        rw [hsplit]
        have : (fun a => ((((E *ᵥ b) (Fin.castAdd m a)) : ℤ) : ℚ)) = 0 := by
          funext a; simp [hEc]
        have h4 : (fun j => ((((E *ᵥ b) (Fin.natAdd k j)) : ℤ) : ℚ)) = fun j => (b j : ℚ) := by
          funext j; simp [hEn]
        rw [this, h4, h0]; simp
      have h5 : (fun i => (((E *ᵥ b) i : ℤ) : ℚ)) = 0 := by
        have := congrArg (fun x => γ⁻¹.val *ᵥ x) h3
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
      apply hb
      funext j
      have := congrFun h5 (Fin.natAdd k j)
      simp only [hEn, Pi.zero_apply] at this
      exact_mod_cast this
    have := hpos _ hw
    rw [← hψeval] at this
    exact_mod_cast this
  · have : f' = QuadForm.orthSum g ψ := QuadForm.eq_of_eval_eq fun y => by
      rw [hfin y]; exact (QuadForm.evalIn_orthSum ℤ g ψ y).symm
    rw [← this]; exact hs

end Local

end QuadFormsKB.Watson1963
