/-
# The finiteness inputs of the theta lift, for positive definite $Q$

**Layer:** the AWS notes' adelic setting over $\mathbb{Q}$ (`AWS/Adelic.lean`, `AWS/Gluing.lean`): $H$ is the Hessian
of $Q$, $O(V_\mathbb{A})$ acts on the lattices $L = g\mathbb{Z}^n \subset \mathbb{Q}^n$, $K_\mathbb{A}$ is the stabilizer of
$\mathbb{Z}^n$ and $O(V)$ is embedded diagonally (`ratPoints`).

**Proves** the two remaining fields of `AWSInputs Q` for positive definite $Q$
($Q(\vec x) > 0$ for all $\vec x \in \mathbb{Q}^n \setminus \{0\}$):
* `finite_classes_of_posDef` (`finite_classes`): the class set $O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A}$ is finite;
* `finite_aut_of_posDef` (`finite_aut`): every $O(V) \cap \alpha K_\mathbb{A}\alpha^{-1}$ is finite;
* `awsInputs_of_posDef`: hence `AWSInputs Q` holds outright, and the consumers D23–D24 hold without it
  (`thetaLift_indicator_eq_posDef`, `thetaLift_classical_posDef`, `thetaLift_one_posDef`,
  `integral_one_eq_mass_posDef`, still relative to the quotient integral `QuotientIntegralInputs`), and a finite family
  of representatives as they require exists (`exists_doset_reps`);
* `finite_autZ`: $\mathrm{Aut}(H) \subseteq \mathrm{GL}_n(\mathbb{Z})$ is finite for a positive definite integral symmetric $H$,
  so D1 (`eisenstein_coeff_self`) holds without its finiteness hypothesis (`eisenstein_coeff_self_uncond`).

*Proof.*
1. *Lattices in the genus are locally unimodular* (`exists_local_unimodular`): if $\alpha\mathbb{Z}^n = g\mathbb{Z}^n$ then at
   every prime $p$, $g = \alpha_p w_p$ with $w_p \in \mathrm{GL}_n(\mathbb{Z}_p)$, so the Gram matrix
   $G = g^{\mathsf T}Hg$ equals $w_p^{\mathsf T}Hw_p$ over $\mathbb{Q}_p$.
2. *Hence* (`gram_isInt`, `det_gram_eq`) $dG$ is integral whenever $dH$ is, and $\det G = \det H$
   ($\det g$ is a $p$-adic unit at every $p$, so $\det g = \pm 1$).
3. *Classes* (Hermite): $dG$ is a positive definite integral matrix of determinant $\det(dH)$, so after a change of
   basis $T \in \mathrm{GL}_n(\mathbb{Z})$ its entries are bounded by $E_n(\det dH)$ (`Hermite.exists_reduced`). Two
   lattices $g\mathbb{Z}^n$, $g'\mathbb{Z}^n$ with the same reduced Gram matrix differ by
   $\gamma = g g'^{-1} \in O(V)(\mathbb{Q})$: finitely many classes.
4. *Automorphisms:* $\gamma \in \mathrm{Aut}(g\mathbb{Z}^n)$ gives $U = g^{-1}\gamma g \in M_n(\mathbb{Z})$ with
   $U^{\mathsf T}GU = G$, so the columns of $U$ are among the finitely many integer vectors $y$ with
   $y^{\mathsf T}(dG)y \le (dG)_{jj}$ (`Lattices.finite_short_vectors`); then $|O(V) \cap \alpha K_\mathbb{A}\alpha^{-1}| =
   |\mathrm{Aut}(\alpha\mathbb{Z}^n)|$ (`card_aut_eq'`).

Positive definiteness is needed for `finite_aut`: for $Q = x_0^2 - 2x_1^2$ the unit $3 + 2\sqrt 2$ gives an automorphism
of $\mathbb{Z}^2$ of infinite order. (`finite_classes` holds for every nondegenerate $Q$, O'Meara 103:4, proved over
number fields as `Lattices.ClassFin.genusClasses_finite_nf`; that layer is not connected to this one.)

*Sources:* Cassels, *Rational Quadratic Forms*, Ch. 9, Thm. 1.1, p. 128 and Lemma 4.1, Cor. 1, p. 139 (finiteness of
classes); Ch. 13, §1, p. 284 (finiteness of $O(f)$ for definite $f$); AWS notes §4.6, p. 64.
-/
import QuadFormsKB.Literature.AWS.Gluing
import QuadFormsKB.Literature.AWS.Measures
import QuadFormsKB.Siegel.HermiteReduction
import QuadFormsKB.Lattices.Finite

open Matrix

namespace QuadFormsKB.AWS

variable {n : ℕ}

/-! ### p-adic and rational integrality -/

section padic

variable {p : ℕ} [Fact p.Prime]

theorem IsIntP.transpose {M : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : IsIntP p M) : IsIntP p Mᵀ :=
  fun i j => hM j i

/-- The determinant of a $p$-integral matrix is $p$-integral. -/
theorem IsIntP.norm_det_le_one {M : Matrix (Fin n) (Fin n) ℚ_[p]} (hM : IsIntP p M) : ‖M.det‖ ≤ 1 := by
  have : M.det ∈ PadicInt.subring p := by
    rw [Matrix.det_apply]
    refine Subring.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => by
      simpa [PadicInt.mem_subring_iff] using hM (σ i) i) _
  simpa [PadicInt.mem_subring_iff] using this

end padic

/-- A nonzero rational number that is a $p$-adic integer, with $p$-integral inverse, at every prime is $\pm 1$. -/
theorem rat_eq_one_or_neg_one {r : ℚ} (hr : r ≠ 0) (h : ∀ p : PrimeIdx, ‖(r : ℚ_[(p : ℕ)])‖ ≤ 1)
    (h' : ∀ p : PrimeIdx, ‖((r⁻¹ : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1) : r = 1 ∨ r = -1 := by
  obtain ⟨a, ha⟩ := (rat_isInt_iff r).mpr h
  obtain ⟨b, hb⟩ := (rat_isInt_iff r⁻¹).mpr h'
  have hab : a * b = 1 := by
    have : (a : ℚ) * b = 1 := by rw [← ha, ← hb, mul_inv_cancel₀ hr]
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h1 | h1
  · left; rw [ha, h1]; simp
  · right; rw [ha, h1]; simp

/-! ### Lattices in the genus of $\mathbb{Z}^n$ -/

section Genus

variable (H : Matrix (Fin n) (Fin n) ℚ)

/-- **Lattices in the genus of $\mathbb{Z}^n$ are locally unimodular:** if $\alpha\mathbb{Z}^n = g\mathbb{Z}^n$
($\alpha \in O(V_\mathbb{A})$, $g \in \mathrm{GL}_n(\mathbb{Q})$), then at every prime $p$ there is
$w \in \mathrm{GL}_n(\mathbb{Z}_p)$ with $g^{\mathsf T}Hg = w^{\mathsf T}Hw$ over $\mathbb{Q}_p$ (namely $w = \alpha_p^{-1}g$). -/
theorem exists_local_unimodular (α : OA H) {g : GL (Fin n) ℚ}
    (hg : (latSMul H (latticeGluing n) α stdLat).1 = latOf g) (p : PrimeIdx) :
    ∃ w : GL (Fin n) ℚ_[(p : ℕ)], IsIntP (p : ℕ) w.val ∧ IsIntP (p : ℕ) w⁻¹.val ∧
      (g.valᵀ * H * g.val).map (algebraMap ℚ ℚ_[(p : ℕ)]) =
        w.valᵀ * H.map (algebraMap ℚ ℚ_[(p : ℕ)]) * w.val := by
  set a : GL (Fin n) ℚ_[(p : ℕ)] := ((α.2 p : orthGroup H ℚ_[(p : ℕ)]) : GL (Fin n) ℚ_[(p : ℕ)]) with ha
  have h1 : latOfP (p : ℕ) (glP (p : ℕ) g) = latOfP (p : ℕ) a := by
    have e := congrArg Subtype.val (loc_latSMul H (latticeGluing n) α stdLat p)
    rw [loc_stdLat, loc_eq_of _ _ hg] at e
    rw [e]
    change (locAct a ⟨latOfP _ 1, 1, rfl⟩).1 = _
    rw [locAct_latOfP, mul_one]
  have hM : (⟨latOfP _ (glP (p : ℕ) g), glP (p : ℕ) g, rfl⟩ : LocLat (p : ℕ) n) = ⟨latOfP _ a, a, rfl⟩ :=
    LocLat.ext h1
  have hstd : locAct (a⁻¹ * glP (p : ℕ) g) (stdLoc (p : ℕ)) = stdLoc (p : ℕ) := by
    apply LocLat.ext
    change (locAct _ ⟨latOfP _ 1, 1, rfl⟩).1 = latOfP _ 1
    rw [locAct_latOfP, mul_one, ← locAct_latOfP, hM, locAct_latOfP, inv_mul_cancel]
  obtain ⟨hw1, hw2⟩ := (locAct_std_iff _).mp hstd
  refine ⟨a⁻¹ * glP (p : ℕ) g, hw1, hw2, ?_⟩
  have hga : glP (p : ℕ) g = a * (a⁻¹ * glP (p : ℕ) g) := by group
  have horth : a.valᵀ * H.map (algebraMap ℚ ℚ_[(p : ℕ)]) * a.val = H.map (algebraMap ℚ ℚ_[(p : ℕ)]) :=
    mem_orthGroup.mp (α.2 p).2
  have hmap : (g.valᵀ * H * g.val).map (algebraMap ℚ ℚ_[(p : ℕ)]) =
      (glP (p : ℕ) g).valᵀ * H.map (algebraMap ℚ ℚ_[(p : ℕ)]) * (glP (p : ℕ) g).val := by
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map]; rfl
  rw [hmap]
  conv_lhs => rw [hga]
  rw [Units.val_mul, transpose_mul]
  calc (a⁻¹ * glP (p : ℕ) g).valᵀ * a.valᵀ * H.map (algebraMap ℚ ℚ_[(p : ℕ)]) *
        (a.val * (a⁻¹ * glP (p : ℕ) g).val)
      = (a⁻¹ * glP (p : ℕ) g).valᵀ * (a.valᵀ * H.map (algebraMap ℚ ℚ_[(p : ℕ)]) * a.val) *
          (a⁻¹ * glP (p : ℕ) g).val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [horth]

/-- **The Gram matrix of a lattice in the genus is as integral as $H$:** if $dH$ has integer entries and
$\alpha\mathbb{Z}^n = g\mathbb{Z}^n$, then $d\,g^{\mathsf T}Hg$ has integer entries. -/
theorem gram_isInt (α : OA H) {g : GL (Fin n) ℚ} (hg : (latSMul H (latticeGluing n) α stdLat).1 = latOf g)
    {d : ℤ} (hd : ∀ i j, ∃ z : ℤ, (d : ℚ) * H i j = z) (i j : Fin n) :
    ∃ z : ℤ, (d : ℚ) * (g.valᵀ * H * g.val) i j = z := by
  rw [rat_isInt_iff]
  intro p
  obtain ⟨w, hw, -, he⟩ := exists_local_unimodular H α hg p
  have hdH : IsIntP (p : ℕ) ((d : ℚ_[(p : ℕ)]) • H.map (algebraMap ℚ ℚ_[(p : ℕ)])) := by
    intro k l
    obtain ⟨z, hz⟩ := hd k l
    have : (d : ℚ_[(p : ℕ)]) * ((H k l : ℚ) : ℚ_[(p : ℕ)]) = ((z : ℚ) : ℚ_[(p : ℕ)]) := by
      rw [← hz]; push_cast; ring
    simp only [Matrix.smul_apply, Matrix.map_apply, eq_ratCast, smul_eq_mul, this, Rat.cast_intCast]
    exact Padic.norm_int_le_one z
  have key := ((hw.transpose.mul hdH).mul hw) i j
  rw [Matrix.mul_smul, Matrix.smul_mul, ← he, Matrix.smul_apply, Matrix.map_apply] at key
  simpa using key

/-- **The Gram matrix of a lattice in the genus has determinant $\det H$** (for $\det H \ne 0$):
$\det(g^{\mathsf T}Hg) = (\det g)^2\det H$, and $\det g$ is a $p$-adic unit at every $p$. -/
theorem det_gram_eq (hH : H.det ≠ 0) (α : OA H) {g : GL (Fin n) ℚ}
    (hg : (latSMul H (latticeGluing n) α stdLat).1 = latOf g) :
    (g.valᵀ * H * g.val).det = H.det := by
  have hg0 : g.val.det ≠ 0 := by
    have := g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin n) (Fin n) ℚ →* ℚ)
    exact this.ne_zero
  -- the p-adic norm of det g is that of det w
  have key : ∀ p : PrimeIdx, ∃ w : GL (Fin n) ℚ_[(p : ℕ)], IsIntP (p : ℕ) w.val ∧ IsIntP (p : ℕ) w⁻¹.val ∧
      ((g.val.det : ℚ) : ℚ_[(p : ℕ)]) ^ 2 = w.val.det ^ 2 := by
    intro p
    obtain ⟨w, hw1, hw2, he⟩ := exists_local_unimodular H α hg p
    refine ⟨w, hw1, hw2, ?_⟩
    have hd := congrArg Matrix.det he
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mul, det_mul, det_transpose, det_mul, det_mul,
      det_transpose, show (H.map (algebraMap ℚ ℚ_[(p : ℕ)])).det = (algebraMap ℚ ℚ_[(p : ℕ)]) H.det from
        (RingHom.map_det _ H).symm] at hd
    have hH' : (algebraMap ℚ ℚ_[(p : ℕ)]) H.det ≠ 0 := by simpa using hH
    rw [map_mul, map_mul] at hd
    have : ((algebraMap ℚ ℚ_[(p : ℕ)]) g.val.det) ^ 2 = w.val.det ^ 2 := by
      apply mul_right_cancel₀ hH'
      linear_combination hd
    simpa using this
  have hunit : ∀ p : PrimeIdx, ‖((g.val.det : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1 ∧
      ‖(((g.val.det)⁻¹ : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1 := by
    intro p
    obtain ⟨w, hw1, hw2, he⟩ := key p
    have hwinv : w⁻¹.val.det * w.val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    have hn : ‖((g.val.det : ℚ) : ℚ_[(p : ℕ)])‖ = ‖w.val.det‖ := by
      have := congrArg norm he
      rw [norm_pow, norm_pow] at this
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    refine ⟨hn ▸ hw1.norm_det_le_one, ?_⟩
    rw [Rat.cast_inv, norm_inv, hn]
    have h1 := hw2.norm_det_le_one
    have hpos : 0 < ‖w.val.det‖ := by
      rw [norm_pos_iff]; intro h0; rw [h0, mul_zero] at hwinv; exact zero_ne_one hwinv
    have : ‖w⁻¹.val.det‖ * ‖w.val.det‖ = 1 := by rw [← norm_mul, hwinv, norm_one]
    rw [inv_le_one₀ hpos]
    nlinarith [norm_nonneg w⁻¹.val.det]
  have hpm := rat_eq_one_or_neg_one hg0 (fun p => (hunit p).1) (fun p => (hunit p).2)
  rw [det_mul, det_mul, det_transpose]
  rcases hpm with h | h <;> rw [h] <;> ring

/-- **Changing the basis of a lattice by $\mathrm{GL}_n(\mathbb{Z})$:** $gT\mathbb{Z}^n = g\mathbb{Z}^n$ for
$T \in \mathrm{GL}_n(\mathbb{Z})$. -/
theorem latOf_mul_intGL (g : GL (Fin n) ℚ) (T : GL (Fin n) ℤ) :
    latOf (g * GeneralLinearGroup.map (Int.castRingHom ℚ) T) = latOf g := by
  set Tq := GeneralLinearGroup.map (Int.castRingHom ℚ) T
  have hint : ∀ (M : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℚ), IsIntVec u →
      IsIntVec (M.map (Int.castRingHom ℚ) *ᵥ u) := by
    intro M u hu i
    choose z hz using hu
    refine ⟨(M *ᵥ z) i, ?_⟩
    have : u = fun k => ((z k : ℤ) : ℚ) := funext hz
    rw [this]
    have := (RingHom.map_mulVec (Int.castRingHom ℚ) M z i)
    simpa [Function.comp_def] using this.symm
  have hTinv : (Tq⁻¹).val = (T⁻¹).val.map (Int.castRingHom ℚ) := by rw [← map_inv]; rfl
  have hT : Tq.val = T.val.map (Int.castRingHom ℚ) := rfl
  ext v
  simp only [latOf, Set.mem_ofPred_eq, _root_.mul_inv_rev, Units.val_mul]
  constructor
  · intro h
    have := hint T.val _ h
    rwa [← hT, mulVec_mulVec, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul] at this
  · intro h
    rw [← mulVec_mulVec, hTinv]
    exact hint _ _ h

end Genus

/-! ### Positive definite forms -/

section PosDef

variable (Q : QuadForm ℚ n)

/-- $\vec x^{\mathsf T}H\vec x = 2Q(\vec x)$ over $\mathbb{Q}$. -/
theorem dot_hessian_self_rat (x : Fin n → ℚ) : x ⬝ᵥ (Q.hessian *ᵥ x) = 2 * Q.evalIn ℚ x := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.hessian, add_mulVec, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec]
  have : Q.coeff.map (algebraMap ℚ ℚ) = Q.coeff := by ext i j; simp
  rw [this]
  ring

theorem hessian_isSymm : Q.hessian.IsSymm := by
  unfold Matrix.IsSymm QuadForm.hessian
  rw [transpose_add, transpose_transpose, add_comm]

variable {Q}

/-- A positive definite $Q$ is nondegenerate: $\det H \ne 0$. -/
theorem det_hessian_ne_zero (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) : Q.hessian.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have := dot_hessian_self_rat Q v
  rw [hHv, dotProduct_zero] at this
  linarith [hQ v hv]

/-- **A common denominator:** some $d > 0$ makes $dH$ integral. -/
theorem exists_int_smul_isInt (M : Matrix (Fin n) (Fin n) ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∀ i j, ∃ z : ℤ, (d : ℚ) * M i j = z := by
  refine ⟨∏ i, ∏ j, ((M i j).den : ℤ), Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by
    exact_mod_cast (M i j).den_pos, fun i j => ?_⟩
  have hdvd : ((M i j).den : ℤ) ∣ ∏ i, ∏ j, ((M i j).den : ℤ) :=
    (Finset.dvd_prod_of_mem (fun j => ((M i j).den : ℤ)) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, ((M i j).den : ℤ)) (Finset.mem_univ i))
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k * (M i j).num, ?_⟩
  rw [hk]
  push_cast
  rw [mul_comm ((M i j).den : ℚ) k, mul_assoc, mul_comm ((M i j).den : ℚ), Rat.mul_den_eq_num]

/-- **The scaled Gram matrix is positive definite integral:** if $A \in M_n(\mathbb{Z})$ equals
$d\,g^{\mathsf T}Hg$ with $d > 0$ and $Q$ positive definite, then $A$ is positive definite. -/
theorem isPosDefInt_of_gram (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) {d : ℤ} (hd : 0 < d)
    (g : GL (Fin n) ℚ) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.map (Int.cast : ℤ → ℚ) = (d : ℚ) • (g.valᵀ * Q.hessian * g.val)) :
    Siegel.Hermite.IsPosDefInt A := by
  have hS : (g.valᵀ * Q.hessian * g.val).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, (hessian_isSymm Q).eq, Matrix.mul_assoc]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    have h1 := congrFun (congrFun hA j) i
    have h2 := congrFun (congrFun hA i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
    rw [Matrix.transpose_apply]
    have : (A j i : ℚ) = A i j := by rw [h1, h2, ← hS.apply j i]
    exact_mod_cast this
  · set xq : Fin n → ℚ := fun i => (x i : ℚ)
    have hcast : ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) = xq ⬝ᵥ (A.map (Int.cast : ℤ → ℚ) *ᵥ xq) := by
      simp [xq, dotProduct, mulVec, Matrix.map_apply]
    have hxq : g.val *ᵥ xq ≠ 0 := by
      intro h0
      apply hx
      have := congrArg (fun v => g⁻¹.val *ᵥ v) h0
      simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
        mulVec_zero] at this
      funext i
      have := congrFun this i
      simpa [xq] using this
    have hpos := hQ _ hxq
    have key : xq ⬝ᵥ (A.map (Int.cast : ℤ → ℚ) *ᵥ xq) = (d : ℚ) * (2 * Q.evalIn ℚ (g.val *ᵥ xq)) := by
      rw [hA, smul_mulVec, dotProduct_smul, smul_eq_mul, ← dot_hessian_self_rat, ← mulVec_mulVec,
        ← mulVec_mulVec, dotProduct_mulVec xq g.valᵀ, vecMul_transpose]
    have : (0 : ℚ) < ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) := by
      rw [hcast, key]
      have : (0 : ℚ) < d := by exact_mod_cast hd
      positivity
    exact_mod_cast this

theorem det_smul_fin (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) : c ^ n * M.det = (c • M).det := by
  rw [Matrix.det_smul, Fintype.card_fin]

/-- $(U^{\mathsf T}GU)_{ij} = u_i^{\mathsf T}Gu_j$ for the columns $u_i, u_j$ of $U$. -/
theorem conj_apply_eq_dot {R : Type*} [CommRing R] (U G : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Uᵀ * G * U) i j = (fun k => U k i) ⬝ᵥ (G *ᵥ fun k => U k j) := by
  rw [Matrix.mul_assoc]
  simp only [mul_apply, transpose_apply, dotProduct, mulVec]

/-- **Reduced Gram matrices** (Hermite): every lattice $\alpha\mathbb{Z}^n$ in the genus has a basis $g$ whose
scaled Gram matrix $d\,g^{\mathsf T}Hg$ is an integral matrix $B$ with entries $|B_{ij}| \le E_n(D)$, where
$D = d^n\det H$ (`Siegel.Hermite.entryBound`). -/
theorem exists_reduced_gram (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) {d : ℤ} (hd : 0 < d)
    (hdH : ∀ i j, ∃ z : ℤ, (d : ℚ) * Q.hessian i j = z) {D : ℤ}
    (hD : (D : ℚ) = (d : ℚ) ^ n * Q.hessian.det) (α : OA Q.hessian) :
    ∃ g : GL (Fin n) ℚ, (latSMul Q.hessian (latticeGluing n) α stdLat).1 = latOf g ∧
      ∃ B : Matrix (Fin n) (Fin n) ℤ, (∀ i j, |B i j| ≤ Siegel.Hermite.entryBound n D) ∧
        B.map (Int.castRingHom ℚ) = (d : ℚ) • (g.valᵀ * Q.hessian * g.val) := by
  obtain ⟨g, hg⟩ := (latSMul Q.hessian (latticeGluing n) α stdLat).2
  have hint := gram_isInt Q.hessian α hg hdH
  choose A hA using hint
  have hAm : (Matrix.of A).map (Int.castRingHom ℚ) = (d : ℚ) • (g.valᵀ * Q.hessian * g.val) := by
    ext i j; simp [hA]
  have hpd := isPosDefInt_of_gram hQ hd g hAm
  have hdet : (Matrix.of A).det = D := by
    have : ((Matrix.of A).det : ℚ) = D := by
      rw [hD, ← det_gram_eq Q.hessian (det_hessian_ne_zero hQ) α hg, det_smul_fin,
        ← hAm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rfl
    exact_mod_cast this
  obtain ⟨T, -, hT⟩ := Siegel.Hermite.exists_reduced n (Matrix.of A) hpd
  refine ⟨g * GeneralLinearGroup.map (Int.castRingHom ℚ) T, by rw [hg, latOf_mul_intGL],
    T.valᵀ * Matrix.of A * T.val, fun i j => hdet ▸ hT i j, ?_⟩
  have hTq : (GeneralLinearGroup.map (Int.castRingHom ℚ) T).val = T.val.map (Int.castRingHom ℚ) := rfl
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, ← hTq, hAm, Units.val_mul, transpose_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- **Lattices with the same Gram matrix are in the same class:** if $\alpha\mathbb{Z}^n = g\mathbb{Z}^n$,
$\alpha'\mathbb{Z}^n = g'\mathbb{Z}^n$ and $g^{\mathsf T}Hg = g'^{\mathsf T}Hg'$, then $\gamma = g'g^{-1} \in O(V)$
carries $\alpha\mathbb{Z}^n$ to $\alpha'\mathbb{Z}^n$, so $O(V)\alpha K_\mathbb{A} = O(V)\alpha' K_\mathbb{A}$. -/
theorem doset_eq_of_gram_eq (H : Matrix (Fin n) (Fin n) ℚ) {α α' : OA H} {g g' : GL (Fin n) ℚ}
    (hg : (latSMul H (latticeGluing n) α stdLat).1 = latOf g)
    (hg' : (latSMul H (latticeGluing n) α' stdLat).1 = latOf g')
    (he : g.valᵀ * H * g.val = g'.valᵀ * H * g'.val) :
    DoubleCoset.mk (ratPoints H) (KA H) α = DoubleCoset.mk (ratPoints H) (KA H) α' := by
  have hid : H.map (algebraMap ℚ ℚ) = H := by ext i j; simp
  have hγ : g' * g⁻¹ ∈ orthGroup H ℚ := by
    rw [mem_orthGroup, hid, Units.val_mul, transpose_mul]
    calc g⁻¹.valᵀ * g'.valᵀ * H * (g'.val * g⁻¹.val)
        = g⁻¹.valᵀ * (g'.valᵀ * H * g'.val) * g⁻¹.val := by simp only [Matrix.mul_assoc]
      _ = (g.val * g⁻¹.val)ᵀ * H * (g.val * g⁻¹.val) := by
          rw [← he, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [← Units.val_mul, mul_inv_cancel]; simp
  set γ : orthGroup H ℚ := ⟨g' * g⁻¹, hγ⟩
  let := latAction' H
  have hsmul : ∀ (a : OA H) (L : Lat n), a • L = latSMul H (latticeGluing n) a L := fun _ _ => rfl
  have h1 : diag H γ • (α • stdLat) = α' • (stdLat : Lat n) := by
    rw [hsmul, hsmul, hsmul, diag_smul']
    apply Lat.ext
    rw [latImage_eq _ g _ hg, hg']
    congr 1
    simp [γ]
  have hk : α'⁻¹ * (diag H γ * α) ∈ KA H := by
    rw [← stabilizer_std' H, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, h1, inv_smul_smul]
  rw [DoubleCoset.eq]
  exact ⟨diag H γ, ⟨γ, rfl⟩, (α'⁻¹ * (diag H γ * α))⁻¹, (KA H).inv_mem hk, by group⟩

/-- **`finite_classes` for positive definite $Q$:** the class set $O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A}$
(the classes in the genus of $\mathbb{Z}^n$, `dosetEquivClassesInGenus'`) is finite. Each class contains a
lattice with a Hermite-reduced scaled Gram matrix (`exists_reduced_gram`), there are finitely many such
matrices (`Lattices.finite_bounded_matrices`), and the Gram matrix determines the class
(`doset_eq_of_gram_eq`). -/
@[kb "hanke2011aws" "§4.6, p. 63 (the double coset space is finite)"]
theorem finite_classes_of_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) :
    Finite (DoubleCoset.Quotient (ratPoints Q.hessian : Set (OA Q.hessian)) (KA Q.hessian)) := by
  classical
  obtain ⟨d, hd, hdH⟩ := exists_int_smul_isInt Q.hessian
  have hdH' := hdH
  choose Hd hHd using hdH'
  have hD : (((Matrix.of Hd).det : ℤ) : ℚ) = (d : ℚ) ^ n * Q.hessian.det := by
    have hm : (Matrix.of Hd).map (Int.castRingHom ℚ) = (d : ℚ) • Q.hessian := by ext i j; simp [hHd]
    rw [det_smul_fin, ← hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  set S := {B : Matrix (Fin n) (Fin n) ℤ | ∀ i j, |B i j| ≤ Siegel.Hermite.entryBound n (Matrix.of Hd).det}
  have hS : Finite S := (Lattices.finite_bounded_matrices n _).to_subtype
  let P : Matrix (Fin n) (Fin n) ℤ → OA Q.hessian → Prop := fun B α =>
    ∃ g : GL (Fin n) ℚ, (latSMul Q.hessian (latticeGluing n) α stdLat).1 = latOf g ∧
      B.map (Int.castRingHom ℚ) = (d : ℚ) • (g.valᵀ * Q.hessian * g.val)
  let f : S → DoubleCoset.Quotient (ratPoints Q.hessian : Set (OA Q.hessian)) (KA Q.hessian) := fun B =>
    if h : ∃ α, P B.1 α then DoubleCoset.mk _ _ h.choose else default
  refine Finite.of_surjective f fun q => ?_
  rw [← DoubleCoset.out_eq' q]
  obtain ⟨g, hg, B, hB, hBe⟩ := exists_reduced_gram hQ hd hdH hD q.out
  have h : ∃ α, P B α := ⟨q.out, g, hg, hBe⟩
  refine ⟨⟨B, hB⟩, ?_⟩
  simp only [f, h, ↓reduceDIte]
  obtain ⟨g', hg', hBe'⟩ := h.choose_spec
  refine doset_eq_of_gram_eq Q.hessian hg' hg ?_
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  exact smul_right_injective _ hd0 (hBe'.symm.trans hBe)

/-- **The automorphism group of a lattice in the genus is finite** (positive definite $Q$): for
$\gamma \in \mathrm{Aut}(g\mathbb{Z}^n)$ the matrix $U = g^{-1}\gamma g$ is integral with $U^{\mathsf T}GU = G$
($G = g^{\mathsf T}Hg$), so its columns $u_j$ satisfy $u_j^{\mathsf T}(dG)u_j = (dG)_{jj}$: finitely many choices
(`Lattices.finite_short_vectors`), and $U$ determines $\gamma$. -/
theorem finite_autLat_of_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) (α : OA Q.hessian) :
    (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) α stdLat)).Finite := by
  obtain ⟨d, hd, hdH⟩ := exists_int_smul_isInt Q.hessian
  set L := latSMul Q.hessian (latticeGluing n) α stdLat
  obtain ⟨g, hg⟩ := L.2
  set G := g.valᵀ * Q.hessian * g.val
  have hint := gram_isInt Q.hessian α hg hdH
  choose A hA using hint
  have hAm : (Matrix.of A).map (Int.castRingHom ℚ) = (d : ℚ) • G := by ext i j; simp [hA, G]
  have hpd := isPosDefInt_of_gram hQ hd g hAm
  have hid : Q.hessian.map (algebraMap ℚ ℚ) = Q.hessian := by ext i j; simp
  -- the integral matrices U = g⁻¹γg
  have hU : ∀ γ : autLat Q.hessian L, ∀ i j, ∃ z : ℤ,
      (g⁻¹.val * ((γ.1 : GL (Fin n) ℚ) * g).val) i j = z := by
    intro γ
    have h := γ.2
    change latImage _ L = L at h
    have h' := congrArg Subtype.val h
    rw [latImage_eq _ g L hg, hg] at h'
    exact isInt_of_latOf_eq h'
  choose V hV using hU
  have hUG : ∀ γ : autLat Q.hessian L,
      (g⁻¹.val * ((γ.1 : GL (Fin n) ℚ) * g).val)ᵀ * G * (g⁻¹.val * ((γ.1 : GL (Fin n) ℚ) * g).val) = G := by
    intro γ
    have horth := mem_orthGroup.mp γ.1.2
    rw [hid] at horth
    have hgg : g.val * g⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [G, Units.val_mul, transpose_mul]
    calc (g.valᵀ * ((γ.1 : GL (Fin n) ℚ)).valᵀ * g⁻¹.valᵀ) * (g.valᵀ * Q.hessian * g.val) *
          (g⁻¹.val * ((γ.1 : GL (Fin n) ℚ).val * g.val))
        = g.valᵀ * ((γ.1 : GL (Fin n) ℚ)).valᵀ * (g.val * g⁻¹.val)ᵀ * Q.hessian * (g.val * g⁻¹.val) *
            ((γ.1 : GL (Fin n) ℚ).val * g.val) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = g.valᵀ * (((γ.1 : GL (Fin n) ℚ)).valᵀ * Q.hessian * (γ.1 : GL (Fin n) ℚ).val) * g.val := by
          rw [hgg]; simp only [transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [horth]
  set Sv := Set.pi Set.univ fun j : Fin n =>
    {y : Fin n → ℤ | y ⬝ᵥ (Matrix.of A *ᵥ y) ≤ Matrix.of A j j}
  have hSv : Sv.Finite := Set.Finite.pi fun j => Lattices.finite_short_vectors hpd _
  have := hSv.to_subtype
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (fun γ => (⟨fun j i => V γ i j, fun j _ => ?_⟩ : Sv)) ?_
  · -- the column condition
    change (fun i => V γ i j) ⬝ᵥ (Matrix.of A *ᵥ fun i => V γ i j) ≤ Matrix.of A j j
    apply le_of_eq
    have hcol : ∀ k, ((V γ k j : ℤ) : ℚ) = (g⁻¹.val * ((γ.1 : GL (Fin n) ℚ) * g).val) k j :=
      fun k => (hV γ k j).symm
    have : (((fun i => V γ i j) ⬝ᵥ (Matrix.of A *ᵥ fun i => V γ i j) : ℤ) : ℚ) =
        ((Matrix.of A j j : ℤ) : ℚ) := by
      have e1 : (((fun i => V γ i j) ⬝ᵥ (Matrix.of A *ᵥ fun i => V γ i j) : ℤ) : ℚ) =
          (fun k => (g⁻¹.val * ((γ.1 : GL (Fin n) ℚ) * g).val) k j) ⬝ᵥ
            ((Matrix.of A).map (Int.castRingHom ℚ) *ᵥ
              fun k => (g⁻¹.val * ((γ.1 : GL (Fin n) ℚ) * g).val) k j) := by
        simp only [← hcol]
        simp [dotProduct, mulVec, Matrix.map_apply]
      have e2 : ((Matrix.of A j j : ℤ) : ℚ) = ((Matrix.of A).map (Int.castRingHom ℚ)) j j := by simp
      rw [e1, e2, ← conj_apply_eq_dot, hAm, Matrix.mul_smul, Matrix.smul_mul, hUG γ]
    exact_mod_cast this
  · intro γ γ' he
    have he' : ∀ i j, V γ i j = V γ' i j := fun i j =>
      congrFun (congrFun (congrArg Subtype.val he) j) i
    have hUe : g⁻¹.val * ((γ.1 : GL (Fin n) ℚ) * g).val = g⁻¹.val * ((γ'.1 : GL (Fin n) ℚ) * g).val := by
      ext i j; rw [hV γ i j, hV γ' i j, he']
    have : (γ.1 : GL (Fin n) ℚ) = γ'.1 := by
      have h2 := congrArg (fun M => g.val * M * g⁻¹.val) hUe
      simp only [← Units.val_mul] at h2
      have h3 : g * (g⁻¹ * ((γ.1 : GL (Fin n) ℚ) * g)) * g⁻¹ =
          g * (g⁻¹ * ((γ'.1 : GL (Fin n) ℚ) * g)) * g⁻¹ := Units.ext h2
      simpa [mul_assoc] using h3
    exact Subtype.ext (Subtype.ext this)

/-- **`finite_aut` for positive definite $Q$:** every $O(V) \cap \alpha K_\mathbb{A}\alpha^{-1}$ is finite.
It has the cardinality of $\mathrm{Aut}(\alpha\mathbb{Z}^n)$ (`card_aut_eq'`), which is finite
(`finite_autLat_of_posDef`) and nonempty, so that cardinality is nonzero. -/
@[kb "hanke2011aws" "§4.6, p. 64 (the groups O(V) ∩ K_{i,A} are finite)"]
theorem finite_aut_of_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) (α : OA Q.hessian) :
    Finite (ratPoints Q.hessian ⊓ conjSub α (KA Q.hessian) : Subgroup _) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_aut_eq' Q.hessian α]
  have := (finite_autLat_of_posDef hQ α).to_subtype
  have h1 : (1 : orthGroup Q.hessian ℚ) ∈
      autLat Q.hessian (latSMul Q.hessian (latticeGluing n) α stdLat) := by
    change latImage _ _ = _
    apply Lat.ext
    simp [latImage]
  have : Nonempty (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) α stdLat)) := ⟨⟨1, h1⟩⟩
  exact Nat.card_pos.ne'

/-- **`AWSInputs Q` holds for positive definite $Q$:** all three fields are proved (`latticeGluing`,
`finite_classes_of_posDef`, `finite_aut_of_posDef`). -/
@[kb "hanke2011aws" "§4.5-§4.6, pp. 61-64"]
theorem awsInputs_of_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) : AWSInputs Q :=
  AWSInputs.ofFinite Q (finite_classes_of_posDef hQ) (finite_aut_of_posDef hQ)

end PosDef

/-! ### D1 without its finiteness hypothesis -/

/-- **The integral automorphism group of a positive definite form is finite:** for a positive definite
integral symmetric $H \in M_n(\mathbb{Z})$, $\mathrm{Aut}(H) = \{X \in \mathrm{GL}_n(\mathbb{Z}) : X^{\mathsf T}HX = H\}$
is finite, since each column $x_j$ of $X$ satisfies $x_j^{\mathsf T}Hx_j = H_{jj}$ (`Lattices.finite_short_vectors`). -/
@[kb "cassels1978" "Ch. 13, §1, p. 284 (O(f) is finite for definite f)"]
theorem finite_autZ {H : Matrix (Fin n) (Fin n) ℤ} (hH : Siegel.Hermite.IsPosDefInt H) : Finite (autZ H) := by
  set Sv := Set.pi Set.univ fun j : Fin n => {y : Fin n → ℤ | y ⬝ᵥ (H *ᵥ y) ≤ H j j}
  have hSv : Sv.Finite := Set.Finite.pi fun j => Lattices.finite_short_vectors hH _
  have := hSv.to_subtype
  refine Finite.of_injective (fun X : autZ H => (⟨fun j i => X.1.val i j, fun j _ => ?_⟩ : Sv)) ?_
  · change (fun i => X.1.val i j) ⬝ᵥ (H *ᵥ fun i => X.1.val i j) ≤ H j j
    rw [← conj_apply_eq_dot, X.2]
  · intro X Y he
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrFun (congrFun (congrArg Subtype.val he) j) i

/-- **D1, (2.8), p. 34, for positive definite forms:** `eisenstein_coeff_self` with its finiteness
hypothesis on the automorphism groups discharged by `finite_autZ`: if the $H_i$ are positive definite
integral symmetric matrices, pairwise inequivalent, of the same nonzero determinant, and $H = H_{i_0}$, then
$a_E(Q) = 1/\mathrm{Mass}(Q)$. -/
@[kb "hanke2011aws" "§2.6, (2.8), p. 34"]
theorem eisenstein_coeff_self_uncond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Matrix (Fin n) (Fin n) ℤ) (i₀ : ι) (h0 : (H i₀).det ≠ 0)
    (hdet : ∀ i, (H i).det = (H i₀).det) (hineq : ∀ i, EquivZ (H i₀) (H i) → i = i₀)
    (hpd : ∀ i, Siegel.Hermite.IsPosDefInt (H i)) :
    (∑ i, (Nat.card (reps (H i₀) (H i)) : ℝ) / Nat.card (autZ (H i))) / mass H = 1 / mass H :=
  eisenstein_coeff_self H i₀ h0 hdet hineq fun i => finite_autZ (hpd i)

/-! ### D23–D24 without `AWSInputs` -/

section ThetaLift

open MeasureTheory
open scoped UpperHalfPlane Classical

variable (Q : QuadForm ℚ n)

/-- **D23: (4.4)–(4.34), pp. 63–66, for positive definite $Q$:** `thetaLift_indicator_eq` with `AWSInputs Q`
discharged (`awsInputs_of_posDef`). Relative only to the quotient integral `QuotientIntegralInputs`:
$$\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,y^{n/4}\,\Theta_{L_j}(z).$$ -/
@[kb "hanke2011aws" "§4.6, (4.4)-(4.34), pp. 63-66"]
theorem thetaLift_indicator_eq_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x)
    [MeasurableSpace (OA Q.hessian)] [MeasurableMul (OA Q.hessian)] {μ : Measure (OA Q.hessian)}
    (inp : QuotientIntegralInputs (ratPoints Q.hessian) (KA Q.hessian) μ)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    inp.I (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α j) stdLat)) : ℂ)⁻¹ *
        (((z.im ^ ((n : ℝ) / 4) : ℝ) : ℂ) *
          thetaSeries Q (latSMul Q.hessian (latticeGluing n) (α j) stdLat) z) :=
  thetaLift_indicator_eq Q inp (awsInputs_of_posDef hQ) α hα hcov hdisj j z

/-- **D23, classical form ((4.35)–(4.37), p. 66), for positive definite $Q$:** `thetaLift_classical` with
`AWSInputs Q` discharged (`awsInputs_of_posDef`); relative only to `QuotientIntegralInputs`:
$$y^{-n/4}\,\Theta(\Phi_{L_j})(g_{\infty,z}) = \frac{1}{|\mathrm{Aut}(L_j)|}\,\Theta_{L_j}(z).$$ -/
@[kb "hanke2011aws" "§4.6, (4.35)-(4.37), p. 66"]
theorem thetaLift_classical_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x)
    [MeasurableSpace (OA Q.hessian)] [MeasurableMul (OA Q.hessian)] {μ : Measure (OA Q.hessian)}
    (inp : QuotientIntegralInputs (ratPoints Q.hessian) (KA Q.hessian) μ)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (j : ι) (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) *
      inp.I (fun h => dosetIndicator (ratPoints Q.hessian) (KA Q.hessian) (α j) h * thetaKernel Q z h) =
      (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian (latticeGluing n) (α j) stdLat) z :=
  thetaLift_classical Q inp (awsInputs_of_posDef hQ) α hα hcov hdisj j z

/-- **D24 (with D23), for positive definite $Q$:** `thetaLift_one` with `AWSInputs Q` discharged
(`awsInputs_of_posDef`); relative only to `QuotientIntegralInputs`, the theta lift of the constant function $1$
is the mass-weighted genus theta series:
$$y^{-n/4}\int_{O(V)\backslash O(V_\mathbb{A})}\theta(g_{\infty,z},h)\,dh
= \sum_{j \in I}\frac{\Theta_{L_j}(z)}{|\mathrm{Aut}(L_j)|}.$$ -/
@[kb "hanke2011aws" "§4.5-§4.6, pp. 62-66"]
theorem thetaLift_one_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x)
    [MeasurableSpace (OA Q.hessian)] [MeasurableMul (OA Q.hessian)] {μ : Measure (OA Q.hessian)}
    (inp : QuotientIntegralInputs (ratPoints Q.hessian) (KA Q.hessian) μ)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian) (hα : ∀ i, (α i).1 = 1)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j)
    (z : ℍ) :
    ((z.im ^ (-(n : ℝ) / 4) : ℝ) : ℂ) * inp.I (thetaKernel Q z) =
      ∑ j, (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α j) stdLat)) : ℂ)⁻¹ *
        thetaSeries Q (latSMul Q.hessian (latticeGluing n) (α j) stdLat) z :=
  thetaLift_one Q inp (awsInputs_of_posDef hQ) α hα hcov hdisj z

/-- **D24 (p. 62 with §2.6), for positive definite $Q$: the volume of $O(V)\backslash O(V_\mathbb{A})$ is the
mass.** `integral_one_eq_mass` for $\Gamma = O(V)$, $K = K_\mathbb{A}$, with its finiteness hypothesis discharged
(`finite_aut_of_posDef`) and $|O(V) \cap \alpha_iK_\mathbb{A}\alpha_i^{-1}| = |\mathrm{Aut}(L_i)|$ (`card_aut_eq'`):
$$\int_{O(V)\backslash O(V_\mathbb{A})} 1\,dh = \sum_{i \in I}\frac{1}{|\mathrm{Aut}(L_i)|}, \qquad L_i = \alpha_i\mathbb{Z}^n.$$
Relative only to `QuotientIntegralInputs`. -/
@[kb "hanke2011aws" "§4.6 with §2.6, p. 34"]
theorem integral_one_eq_mass_posDef (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x)
    [MeasurableSpace (OA Q.hessian)] [MeasurableMul (OA Q.hessian)] {μ : Measure (OA Q.hessian)}
    (inp : QuotientIntegralInputs (ratPoints Q.hessian) (KA Q.hessian) μ)
    {ι : Type*} [Fintype ι] (α : ι → OA Q.hessian)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian))
    (hdisj : ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
      DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j) :
    inp.I (fun _ => 1) =
      ∑ i, (Nat.card (autLat Q.hessian (latSMul Q.hessian (latticeGluing n) (α i) stdLat)) : ℂ)⁻¹ := by
  rw [integral_one_eq_mass inp α hcov hdisj fun i => finite_aut_of_posDef hQ (α i)]
  simp only [card_aut_eq']

/-- **Finitely many class representatives with trivial archimedean component** (p. 63, "to simplify our lives
we choose the $\alpha_{i,\mathbb{A}}$ to have trivial archimedean components"), for positive definite $Q$: there
is a finite family $(\alpha_i)_{i \in I}$ in $O(V_\mathbb{A})$ with $\alpha_{i,\infty} = 1$ whose double cosets
$O(V)\alpha_iK_\mathbb{A}$ cover $O(V_\mathbb{A})$ and are pairwise distinct: the hypotheses `hα`, `hcov`,
`hdisj` of D23–D24 can be met. -/
@[kb "hanke2011aws" "§4.6, p. 63"]
theorem exists_doset_reps (hQ : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x) :
    ∃ (ι : Type) (_ : Fintype ι) (α : ι → OA Q.hessian), (∀ i, (α i).1 = 1) ∧
      (∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) (ratPoints Q.hessian) (KA Q.hessian)) ∧
      ∀ i j, DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α i) =
        DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (α j) → i = j := by
  have := finite_classes_of_posDef hQ
  choose a ha1 ham using fun q : DoubleCoset.Quotient (ratPoints Q.hessian : Set (OA Q.hessian)) (KA Q.hessian) =>
    exists_rep_infty_one Q.hessian q.out
  refine ⟨_, Fintype.ofFinite _, a, ha1, fun g => ⟨DoubleCoset.mk _ _ g, ?_⟩, fun i j h => ?_⟩
  · have e : DoubleCoset.mk (ratPoints Q.hessian) (KA Q.hessian) (a (DoubleCoset.mk _ _ g)) =
        DoubleCoset.mk _ _ g := by rw [ham, DoubleCoset.out_eq']
    obtain ⟨h, hh, k, hk, e'⟩ := DoubleCoset.eq.mp e
    exact DoubleCoset.mem_doubleCoset.mpr ⟨h, hh, k, hk, e'⟩
  · rwa [ham, ham, DoubleCoset.out_eq', DoubleCoset.out_eq'] at h

end ThetaLift

end QuadFormsKB.AWS
