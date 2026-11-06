/-
# Hanke 2005, (3.3) at odd places: the self-density of $\langle u_0,\dots,u_{a-1}\rangle\perp\pi T$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Let $R$ be a discrete valuation ring with finite residue field and uniformizer $\pi\nmid2$. Let $u_0,\dots,u_{a-1}$ be units
and $T$ a nondegenerate form all of whose coefficients are divisible by $\pi$ (for instance $T=\pi W$ with $W$ unimodular).
Write $Q=\langle u_0,\dots,u_{a-1}\rangle\perp T$ (`unitSum`). Then
$$\beta_\pi(Q,Q)=\beta_\pi(\langle u\rangle,\langle u\rangle)\,\beta_\pi(T,T)\qquad(\texttt{localDensityForm\_unitSum}).$$
*Proof.* Peel off $\langle u_0\rangle$ by Weil's identity at a unit (`localIdentity_unit`, valid for every $Q'$):
$\beta(Q,Q)=\beta(Q',Q')\,\beta(Q,u_0)$. The density of the unit $u_0$ by $Q$ is the residue-field count
$\#\{x\in k^{n}:\bar Q(x)=\bar u_0\}/q^{n-1}$ (`localDensityForm_eq_of_isUnit`), and the variables of $T$ do not enter
$\bar Q$ (`Nc_unitSum`), so this density is the one for $\langle u\rangle$ alone.
-/
import QuadFormsKB.Tamagawa.TernaryBadDVR

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadForm

section Product

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **$\langle u_0,\dots,u_{a-1}\rangle\perp T$**: $a$ split-off rank-one summands in front of $T$ (in $b+a$ variables). -/
def unitSum {b : ℕ} (T : QuadForm R b) : (a : ℕ) → (Fin a → R) → QuadForm R (b + a)
  | 0, _ => T
  | a + 1, u => splitForm (u 0) (unitSum T a (Fin.tail u))

/-- The diagonal form is the split form of its first entry and the diagonal form of the rest. -/
theorem diag_succ {a : ℕ} (u : Fin (a + 1) → R) :
    QuadForm.diag u = splitForm (u 0) (QuadForm.diag (Fin.tail u)) := by
  refine QuadForm.ext ?_
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [QuadForm.diag, splitForm_coeff, Matrix.diagonal_apply, Fin.succ_ne_zero, Fin.tail,
      (Fin.succ_ne_zero _).symm, Fin.succ_inj]

theorem nondeg_unitSum {b : ℕ} (T : QuadForm R b) (hT : T.Nondegenerate) (h2 : (2 : R) ≠ 0) :
    ∀ (a : ℕ) (u : Fin a → R), (∀ i, u i ≠ 0) → (unitSum T a u).Nondegenerate
  | 0, _, _ => hT
  | a + 1, u, hu => by
    have ih := nondeg_unitSum T hT h2 a (Fin.tail u) (fun i => hu _)
    show (splitForm (u 0) (unitSum T a (Fin.tail u))).Nondegenerate
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero h2 (hu 0)) ih

/-! ### Counting points of the reduction -/

/-- The number of $x\in K^n$ with $Q(x)=c$ ($K$ an $R$-algebra, e.g. the residue ring $R/\pi$). -/
def Nc (K : Type*) [CommRing K] [Algebra R K] {n : ℕ} (c : K) (Q : QuadForm R n) : ℕ :=
  Nat.card {x : Fin n → K // Q.evalIn K x = c}

theorem Nc_split (K : Type*) [CommRing K] [Algebra R K] [Fintype K] {n : ℕ} (m : R) (Q' : QuadForm R n) (c : K) :
    Nc K c (splitForm m Q') = ∑ t : K, Nc K (c - algebraMap R K m * t * t) Q' := by
  classical
  unfold Nc
  have e : {x : Fin (n + 1) → K // (splitForm m Q').evalIn K x = c} ≃
      Σ t : K, {y : Fin n → K // Q'.evalIn K y = c - algebraMap R K m * t * t} :=
    { toFun := fun x => ⟨x.1 0, Fin.tail x.1, by
        have h := x.2
        rw [← Fin.cons_self_tail x.1, evalIn_splitForm] at h
        change Q'.evalIn K (Fin.tail x.1) = _
        rw [eq_sub_iff_add_eq, add_comm]; exact h⟩
      invFun := fun p => ⟨Fin.cons p.1 p.2.1, by
        rw [evalIn_splitForm, p.2.2]; ring⟩
      left_inv := fun x => Subtype.ext (Fin.cons_self_tail x.1)
      right_inv := fun p => by
        obtain ⟨t, y, hy⟩ := p
        exact Sigma.ext (by simp) ((Subtype.heq_iff_coe_eq (fun z => by simp)).2 (by simp)) }
  rw [Nat.card_congr e, Nat.card_sigma]

/-- A form with all coefficients in $\pi R$ vanishes on $(R/\pi)^n$. -/
theorem evalIn_eq_zero_of_dvd {n : ℕ} (T : QuadForm R n) (π : R) (hT : ∀ i j, ∃ c, T.coeff i j = π * c)
    (x : Fin n → R ⧸ Ideal.span {π ^ 1}) : T.evalIn (R ⧸ Ideal.span {π ^ 1}) x = 0 := by
  have hz : (Ideal.Quotient.mk (Ideal.span {π ^ 1}) π) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self π
  rw [QuadForm.evalIn_eq_dotProduct]
  have : T.coeff.map (algebraMap R (R ⧸ Ideal.span {π ^ 1})) = 0 := by
    ext i j
    obtain ⟨c, hc⟩ := hT i j
    simp only [Matrix.map_apply, hc, Matrix.zero_apply]
    rw [map_mul]
    change Ideal.Quotient.mk _ π * _ = 0
    rw [hz, zero_mul]
  rw [this]; simp

open Classical in
theorem Nc_of_eval_zero (K : Type*) [CommRing K] [Algebra R K] [Finite K] {n : ℕ} (S : QuadForm R n)
    (hS : ∀ x, S.evalIn K x = 0) (c : K) :
    Nc K c S = if c = 0 then Nat.card K ^ n else 0 := by
  unfold Nc
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl, Nat.card_congr (Equiv.subtypeUnivEquiv hS), Nat.card_fun]
    simp
  · rw [if_neg hc]
    have : IsEmpty {x : Fin n → K // S.evalIn K x = c} := ⟨fun x => hc (x.2.symm.trans (hS x.1))⟩
    exact Nat.card_of_isEmpty

/-- **The count of points of the reduction does not see $T$**: for $T\equiv0\bmod\pi$,
$\#\{x\in k^{b+a}:(\langle u\rangle\perp T)(x)=c\}=q^b\,\#\{x\in k^a:\langle u\rangle(x)=c\}$, $k=R/\pi$. -/
theorem Nc_unitSum [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) {b : ℕ} (T : QuadForm R b)
    (hT : ∀ i j, ∃ c, T.coeff i j = π * c) :
    ∀ (a : ℕ) (u : Fin a → R) (c : R ⧸ Ideal.span {π ^ 1}),
      Nc (R ⧸ Ideal.span {π ^ 1}) c (unitSum T a u) =
        q R ^ b * Nc (R ⧸ Ideal.span {π ^ 1}) c (QuadForm.diag u) := by
  have hfin := finite_quot_pow π hπ 1
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  intro a
  induction a with
  | zero =>
    intro u c
    have h1 : ∀ x, (QuadForm.diag u).evalIn (R ⧸ Ideal.span {π ^ 1}) x = 0 := by
      intro x
      rw [QuadForm.evalIn_eq_dotProduct]; simp
    show Nc _ c T = _
    rw [Nc_of_eval_zero _ T (evalIn_eq_zero_of_dvd T π hT) c, Nc_of_eval_zero _ _ h1 c, hcard]
    split_ifs <;> simp
  | succ a ih =>
    intro u c
    letI := Fintype.ofFinite (R ⧸ Ideal.span {π ^ 1})
    show Nc _ c (splitForm (u 0) (unitSum T a (Fin.tail u))) = _
    rw [diag_succ u, Nc_split, Nc_split, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => ih _ _

/-- **$\beta_\pi(Q,m)$ for a unit $m$ is a count over the residue ring:** $\beta_\pi(Q,m)=\#\{x\in k^n:Q(x)=m\}/q^{n-1}$ when
$2m$ is a unit and $n\ge1$. -/
theorem localDensity_eq_Nc [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) {n : ℕ}
    (Q : QuadForm R n) (hn : 1 ≤ n) {m : R} (hm : IsUnit (2 * m)) :
    localDensity Q π m = (Nc (R ⧸ Ideal.span {π ^ 1}) (Ideal.Quotient.mk _ m) Q : ℝ) / (q R : ℝ) ^ (n - 1) := by
  have hU : IsUnit (unary m).hessian.det := by
    have : (unary m).hessian.det = 2 * m := by
      simp [hessian, unary, QuadForm.diag, Matrix.det_unique]; ring
    rw [this]; exact hm
  rw [← localDensityForm_unary, localDensityForm_eq_of_isUnit Q (unary m) π hπ hU hn, repCountForm_unary,
    show n * 1 - 1 * (1 + 1) / 2 = n - 1 by omega]
  rfl

/-- $\beta_\pi$ of the form in zero variables is $1$. -/
theorem localDensityForm_zero (Q : QuadForm R 0) (π : R) : localDensityForm Q Q π = 1 := by
  unfold localDensityForm
  have : ∀ k : ℕ, (repCountForm Q Q π k : ℝ) / (q R : ℝ) ^ (k * (0 * 0 - 0 * (0 + 1) / 2)) = 1 := by
    intro k
    have hc : repCountForm Q Q π k = 1 := by
      unfold repCountForm
      have : Unique {X : Matrix (Fin 0) (Fin 0) (R ⧸ Ideal.span {π ^ k}) //
          (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).compMat X = Q.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))} :=
        { default := ⟨0, QuadForm.ext (Subsingleton.elim _ _)⟩
          uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
      exact Nat.card_unique
    simp [hc]
  simp only [this]
  exact (tendsto_const_nhds (x := (1 : ℝ))).limUnder_eq

/-- **The self-density of $\langle u_0,\dots,u_{a-1}\rangle\perp T$** (units $u_i$, $\pi\nmid2$, $T$ nondegenerate with all
coefficients divisible by $\pi$): $\beta(Q,Q)=\beta(\langle u\rangle,\langle u\rangle)\,\beta(T,T)$. -/
theorem localDensityForm_unitSum [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    {b : ℕ} (T : QuadForm R b) (hTnd : T.Nondegenerate) (hT : ∀ i j, ∃ c, T.coeff i j = π * c) :
    ∀ (a : ℕ) (u : Fin a → R), (∀ i, IsUnit (u i)) →
      localDensityForm (unitSum T a u) (unitSum T a u) π =
        localDensityForm (QuadForm.diag u) (QuadForm.diag u) π * localDensityForm T T π := by
  have h2u : IsUnit (2 : R) := dvr_isUnit_of_not_dvd hπ h2
  have h20 : (2 : R) ≠ 0 := h2u.ne_zero
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  intro a
  induction a with
  | zero =>
    intro u _
    rw [localDensityForm_zero (QuadForm.diag u) π, one_mul]
    rfl
  | succ a ih =>
    intro u hu
    set u' : Fin a → R := Fin.tail u with hu'
    have hu'u : ∀ i, IsUnit (u' i) := fun i => hu _
    have hm : IsUnit (2 * u 0) := h2u.mul (hu 0)
    have hQp : (unitSum T a u').Nondegenerate := nondeg_unitSum T hTnd h20 a u' fun i => (hu'u i).ne_zero
    have hD' : (QuadForm.diag u').Nondegenerate := by
      rw [QuadForm.Nondegenerate, det_hessian_diag]
      exact mul_ne_zero (pow_ne_zero _ h20) (Finset.prod_ne_zero_iff.mpr fun i _ => (hu'u i).ne_zero)
    have e1 := localIdentity_unit hπ hm h20 _ hQp
    have e2 := localIdentity_unit hπ hm h20 _ hD'
    rw [← diag_succ u] at e2
    have hih := ih u' hu'u
    have d1 : localDensity (splitForm (u 0) (unitSum T a u')) π (u 0) =
        (q R : ℝ) ^ b * (Nc (R ⧸ Ideal.span {π ^ 1}) (Ideal.Quotient.mk _ (u 0)) (QuadForm.diag u) : ℝ) /
          (q R : ℝ) ^ (b + a) := by
      have := localDensity_eq_Nc hπ (unitSum T (a + 1) u) (by omega) hm
      have hN := Nc_unitSum hπ T hT (a + 1) u (Ideal.Quotient.mk _ (u 0))
      change localDensity (unitSum T (a + 1) u) π (u 0) = _
      rw [this, hN]
      push_cast
      rw [show b + (a + 1) - 1 = b + a by omega]
    have d2 : localDensity (QuadForm.diag u) π (u 0) =
        (Nc (R ⧸ Ideal.span {π ^ 1}) (Ideal.Quotient.mk _ (u 0)) (QuadForm.diag u) : ℝ) / (q R : ℝ) ^ a := by
      rw [localDensity_eq_Nc hπ (QuadForm.diag u) (by omega) hm]
      simp only [Nat.add_sub_cancel]
    change localDensityForm (splitForm (u 0) (unitSum T a u')) (splitForm (u 0) (unitSum T a u')) π = _
    rw [← e1, d1, hih, ← e2, d2, pow_add]
    field_simp

end Product

end QuadFormsKB.Hanke2005
