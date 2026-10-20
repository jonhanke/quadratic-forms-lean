/-
# Kneser neighbours, part 8: the neighbour graph on classes and certified closure

**Layer:** integral forms (`QuadForm ℤ n`) and lattices in $\mathbb{Q}^n$ (`Siegel/Neighbors.lean`).

**Defines**
- `IsNbrForm p Q Q'`: $Q'$ is the Gram form, in some basis, of a $p$-neighbour of $(\mathbb{Z}^n, Q)$;
- `NbrStep p`, `NbrReach p`: one step / the reflexive-transitive closure of the **$p$-neighbour graph on
  $\mathrm{GL}_n(\mathbb{Z})$-classes** (a step from $Q$ to any form equivalent to a neighbour form of $Q$);
- `KneserConnected p Q`: every form in the genus of $Q$ is reachable from $Q$ (the conclusion of Kneser's theorem when the
  genus is one spinor genus; `Lattices/Kneser.lean`).

**Proves**
- `IsNbrForm.of_intEquiv`: the neighbour forms of equivalent forms agree (so the graph lives on classes);
- `IsNbrForm.sameGenus`: neighbour forms are in the genus (for $p$ odd, $p \nmid \det H$);
- `exists_intEquiv_of_cover` (**certified neighbour closure**): if a list of neighbour certificates `cs` covers every
  isotropic line of $\mathbb{F}_p^n$ (a finite, decidable check over `Gen.allVecs`), then **every** $p$-neighbour form of $Q$
  is equivalent to one of the certified forms;
- `exists_intEquiv_of_reach`: if a set $S$ of forms is closed under neighbour steps, everything reachable from $S$ is
  equivalent to a member of $S$; with `KneserConnected` this gives `genusClasses_eq_of_closed`, the **closure
  completeness criterion** of the neighbour method (Kneser 1957, §2; Scharlau–Hemkemeier 1998, §2).
-/
import QuadFormsKB.Siegel.KneserGen

open Matrix

namespace QuadFormsKB.Siegel.Kneser

open QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Neighbour forms -/

/-- **$Q'$ is a $p$-neighbour form of $Q$:** for some $g \in \mathrm{GL}_n(\mathbb{Q})$, the lattice $g\mathbb{Z}^n$ is a $p$-neighbour of
$(\mathbb{Z}^n, Q)$ (`IsNeighbor`) and $Q'(\vec{x}) = Q(g\vec{x})$ on $\mathbb{Q}^n$ ($Q'$ is the Gram form of the neighbour in the basis
given by the columns of $g$). -/
@[kb "kneser1957" "§1, Nachbarn [unverified]"]
def IsNbrForm (p : ℕ) (Q Q' : QuadForm ℤ n) : Prop :=
  ∃ g : Matrix (Fin n) (Fin n) ℚ, g.det ≠ 0 ∧ IsNeighbor Q p (imgLat g) ∧
    ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)

/-- **One step of the $p$-neighbour graph on classes:** $Q''$ is equivalent to a $p$-neighbour form of $Q$. -/
def NbrStep (p : ℕ) (Q Q'' : QuadForm ℤ n) : Prop := ∃ Q', IsNbrForm p Q Q' ∧ IntEquiv Q' Q''

/-- **Reachability in the $p$-neighbour graph** (reflexive-transitive closure of `NbrStep`). -/
def NbrReach (p : ℕ) : QuadForm ℤ n → QuadForm ℤ n → Prop := Relation.ReflTransGen (NbrStep p)

/-- **Kneser connectivity of the genus of $Q$ at $p$:** every form in the genus of $Q$ is reachable from $Q$ by $p$-neighbour
steps. Kneser's theorem (`Lattices/Kneser.lean`) gives this for $n \ge 3$, $p \nmid 2\det H$, when the genus is a single spinor
genus. -/
@[kb "kneser1957" "Satz 2 [unverified]"]
def KneserConnected (p : ℕ) (Q : QuadForm ℤ n) : Prop := ∀ Q', SameGenus Q Q' → NbrReach p Q Q'

section Transport

theorem toAddSubgroup_imgLat_mul (A g : Matrix (Fin n) (Fin n) ℚ) :
    (imgLat (A * g)).toAddSubgroup = (imgLat g).toAddSubgroup.map (Matrix.mulVecLin A).toAddMonoidHom := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, mem_imgLat, LinearMap.toAddMonoidHom_coe,
    Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨g *ᵥ cv c, ⟨c, rfl⟩, by rw [mulVec_mulVec]⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩; exact ⟨c, by rw [mulVec_mulVec]⟩

/-- The rational image of an integer matrix. -/
abbrev qM (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ := M.map (Int.castRingHom ℚ)

theorem imgLat_qM (U : GL (Fin n) ℤ) : imgLat (qM U.val) = stdLat n := by
  ext x
  simp only [mem_imgLat, mem_stdLat]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨U.val *ᵥ c, cv_mulVec _ _⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(U⁻¹).val *ᵥ y, ?_⟩
    rw [cv_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem det_qM (U : GL (Fin n) ℤ) : (qM U.val).det ≠ 0 := by
  have h : (qM U.val).det = (U.val.det : ℚ) := by
    change ((Int.castRingHom ℚ).mapMatrix U.val).det = _
    rw [← RingHom.map_det]; rfl
  rw [h]
  have := Matrix.isUnit_iff_isUnit_det U.val |>.mp U.isUnit
  rcases Int.isUnit_iff.mp this with h1 | h1 <;> simp [h1]

/-- The integer identity $Q_1(M\vec{x}) = Q(\vec{x})$ holds over $\mathbb{Q}$ too. -/
theorem evalIn_qM {Q₁ Q : QuadForm ℤ n} {M : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ x, Q₁.eval (M *ᵥ x) = Q.eval x) (x : Fin n → ℚ) :
    Q₁.evalIn ℚ (qM M *ᵥ x) = Q.evalIn ℚ x := by
  have hH := (eval_mulVec_eq_iff_hessian Q₁ Q M).mp h
  have hT : (Int.castRingHom ℚ).mapMatrix Mᵀ = (qM M)ᵀ := by ext i j; rfl
  have hHq : Q.hessian.map (algebraMap ℤ ℚ) = (qM M)ᵀ * Q₁.hessian.map (algebraMap ℤ ℚ) * qM M := by
    change (Int.castRingHom ℚ).mapMatrix Q.hessian = (qM M)ᵀ * (Int.castRingHom ℚ).mapMatrix Q₁.hessian * qM M
    rw [← hH, map_mul, map_mul, hT]; rfl
  have h1 := two_mul_evalIn (K := ℚ) Q x
  have h2 := two_mul_evalIn (K := ℚ) Q₁ (qM M *ᵥ x)
  rw [hHq, dotProduct_conj] at h1
  linarith

/-- **Neighbour forms of equivalent forms:** if $Q_1(U\vec{x}) = Q(\vec{x})$ with $U \in \mathrm{GL}_n(\mathbb{Z})$ and $Q'$ is a $p$-neighbour form
of $Q$, then $Q'$ is a $p$-neighbour form of $Q_1$ (the neighbour $g\mathbb{Z}^n$ of $(\mathbb{Z}^n, Q)$ maps to the neighbour $Ug\mathbb{Z}^n$ of
$(\mathbb{Z}^n, Q_1)$ with the same Gram form). -/
theorem IsNbrForm.of_intEquiv {p : ℕ} {Q₁ Q Q' : QuadForm ℤ n} (h₁ : IntEquiv Q₁ Q) (h : IsNbrForm p Q Q') :
    IsNbrForm p Q₁ Q' := by
  obtain ⟨U, hU⟩ := h₁
  obtain ⟨g, hg, hL, hQ'⟩ := h
  have hinj : Function.Injective (Matrix.mulVecLin (qM U.val)).toAddMonoidHom := by
    intro x y hxy
    have := congrArg (fun z => qM (U⁻¹).val *ᵥ z) hxy
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, mulVec_mulVec] at this
    have e : qM (U⁻¹).val * qM U.val = 1 := by
      rw [qM, qM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one] <;> simp
    rwa [e, one_mulVec, one_mulVec] at this
  have hstd : (stdLat n).toAddSubgroup.map (Matrix.mulVecLin (qM U.val)).toAddMonoidHom = (stdLat n).toAddSubgroup := by
    have := toAddSubgroup_imgLat_mul (qM U.val) 1
    rw [Matrix.mul_one, imgLat_qM, ← stdLat_eq_imgLat_one] at this
    exact this.symm
  refine ⟨qM U.val * g, ?_, ⟨?_, ?_, ?_⟩, fun x => ?_⟩
  · rw [det_mul]; exact mul_ne_zero (det_qM U) hg
  · rw [toAddSubgroup_imgLat_mul, ← hstd, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hL.relIndex_std
  · rw [toAddSubgroup_imgLat_mul, ← hstd, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hL.relIndex_self
  · rintro _ ⟨c, rfl⟩
    rw [← mulVec_mulVec, evalIn_qM hU]
    exact hL.integral _ ⟨c, rfl⟩
  · rw [hQ', ← mulVec_mulVec, evalIn_qM hU]

/-- **Neighbour forms are in the genus** ($p$ odd, $p \nmid \det H$; AWS notes, Thm. 1.10.3(1)). -/
theorem IsNbrForm.sameGenus {p : ℕ} [Fact p.Prime] {Q Q' : QuadForm ℤ n} (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (h : IsNbrForm p Q Q') : SameGenus Q Q' := by
  obtain ⟨g, hg, hL, hQ'⟩ := h
  exact sameGenus_of_neighbor hp2 hdet hg hL hQ'

/-- A valid neighbour certificate gives a neighbour form. -/
theorem NbCert.isNbrForm {p : ℕ} [Fact p.Prime] {Q Q' : QuadForm ℤ n} {c : NbCert n}
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (h : c.Valid Q Q' p) : IsNbrForm p Q Q' := by
  have hv0 : red p c.v ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.1
    intro h0; exact hi ((red_eq_zero_iff c.v).mp h0 i)
  refine ⟨c.g p, NbCert.det_g_ne_zero h, ?_, NbCert.evalIn_eq h⟩
  rw [NbCert.imgLat_eq_nbLat h]; exact isNeighbor_nbLat hdet h.1 hv0

end Transport

/-! ### Bases of the same lattice differ by $\mathrm{GL}_n(\mathbb{Z})$ -/

theorem cv_single (j : Fin n) : cv (Pi.single j (1 : ℤ)) = (Pi.single j (1 : ℚ) : Fin n → ℚ) := by
  ext i; by_cases h : i = j <;> simp [cv, h]

theorem exists_int_of_imgLat_le {g h : Matrix (Fin n) (Fin n) ℚ} (hle : imgLat h ≤ imgLat g) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, h = g * qM C := by
  choose c hc using fun j => hle ⟨Pi.single j 1, rfl⟩
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext i j
  have := congrFun (hc j) i
  rw [cv_single, Matrix.mulVec_single_one] at this
  rw [Matrix.col_apply] at this
  rw [this, Matrix.mul_apply]
  simp only [mulVec, dotProduct, cv, Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom]

/-- **Two bases of one lattice differ by $\mathrm{GL}_n(\mathbb{Z})$:** if $g\mathbb{Z}^n = h\mathbb{Z}^n$ and $\det g \ne 0$, then $h = gU$ with
$U \in \mathrm{GL}_n(\mathbb{Z})$. -/
theorem exists_gl_of_imgLat_eq {g h : Matrix (Fin n) (Fin n) ℚ} (hg : g.det ≠ 0) (he : imgLat g = imgLat h) :
    ∃ U : GL (Fin n) ℤ, h = g * qM U.val := by
  obtain ⟨C, hC⟩ := exists_int_of_imgLat_le he.ge
  obtain ⟨D, hD⟩ := exists_int_of_imgLat_le he.le
  have hCD : C * D = 1 := by
    have e : g * qM (C * D) = g * 1 := by
      rw [Matrix.mul_one, qM, Matrix.map_mul, ← Matrix.mul_assoc, ← hC, ← hD]
    have hgU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hg)
    have e2 := hgU.mul_left_cancel e
    have : (C * D).map (Int.castRingHom ℚ) = (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ) := by
      rw [Matrix.map_one _ (map_zero _) (map_one _)]; exact e2
    exact Matrix.map_injective (Int.cast_injective) this
  exact ⟨⟨C, D, hCD, mul_eq_one_comm.mp hCD⟩, hC⟩

/-! ### Certified closure -/

theorem eval_dvd_of_congr {Q : QuadForm ℤ n} {p : ℕ} [Fact p.Prime] {u v : Fin n → ℤ}
    (h : ∀ i, (p : ℤ) ∣ u i - v i) : (p : ℤ) ∣ Q.eval u - Q.eval v := by
  have hr : red p u = red p v := by
    ext i; simp only [red]; exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by
      have := h i; rw [← dvd_neg, neg_sub] at this; exact this)
  have := congrArg (qv Q p) hr
  rw [qv_red, qv_red] at this
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this.symm

/-- **Certified neighbour closure.** Let $p$ be an odd prime, $p \nmid \det H$, and `cs` a list of pairs (neighbour
certificate, form) such that
- `hvalid`: each certificate is valid (`NbCert.Valid`), so each listed form is a $p$-neighbour form of $Q$;
- `hcover`: every $\vec{u} \in \{0, \dots, p-1\}^n$ with $\vec{u} \not\equiv 0$ and $p \mid Q(\vec{u})$ is $\equiv a\vec{v}_c \pmod p$ for some
  certificate $c$ and $0 \le a < p$ (the certificates cover all isotropic lines).

Both hypotheses are finite and decidable. Then **every** $p$-neighbour form of $Q$ is equivalent to a listed form. -/
@[kb "schulzepillot1991" "§2 (neighbour generation)"]
theorem exists_intEquiv_of_cover {Q : QuadForm ℤ n} {p : ℕ} [hp : Fact p.Prime]
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (cs : List (NbCert n × QuadForm ℤ n))
    (hvalid : ∀ c ∈ cs, c.1.Valid Q c.2 p)
    (hcover : ∀ u ∈ Gen.allVecs p n, (∃ i, ¬ (p : ℤ) ∣ u i) → (p : ℤ) ∣ Q.eval u →
      ∃ c ∈ cs, ∃ a < p, ∀ i, (p : ℤ) ∣ u i - (a : ℤ) * c.1.v i)
    {Q' : QuadForm ℤ n} (h : IsNbrForm p Q Q') : ∃ c ∈ cs, IntEquiv c.2 Q' := by
  obtain ⟨g, hg, hL, hQ'⟩ := h
  obtain ⟨v, hv, hv0, hLv⟩ := exists_eq_nbLat hdet hL
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  set u : Fin n → ℤ := fun i => v i % p
  have huv : ∀ i, (p : ℤ) ∣ u i - v i := fun i => by
    simp only [u]; rw [Int.emod_def]; exact ⟨-(v i / p), by ring⟩
  have hu : u ∈ Gen.allVecs p n := Gen.mem_allVecs u fun i =>
    ⟨Int.emod_nonneg _ hpZ.ne', Int.emod_lt_of_pos _ hpZ⟩
  have hu0 : ∃ i, ¬ (p : ℤ) ∣ u i := by
    by_contra hc
    push Not at hc
    exact hv0 ((red_eq_zero_iff v).mpr fun i => by
      have := dvd_sub (hc i) (huv i); simpa using this)
  have huQ : (p : ℤ) ∣ Q.eval u := by
    have h1 := eval_dvd_of_congr (Q := Q) huv
    have h2 : (p : ℤ) ∣ Q.eval v := (dvd_pow_self _ two_ne_zero).trans hv
    have := dvd_add h1 h2; simpa using this
  obtain ⟨c, hc, a, ha, hua⟩ := hcover u hu hu0 huQ
  have hcv := hvalid c hc
  -- red v = a • red v_c
  have hred : red p v = (a : ZMod p) • red p c.1.v := by
    ext i
    simp only [red, Pi.smul_apply, smul_eq_mul]
    have : (p : ℤ) ∣ v i - a * c.1.v i := by
      have := dvd_sub (hua i) (huv i); simpa using this
    have e := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by rw [← dvd_neg, neg_sub]; exact this)
    rw [e]; push_cast; ring
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hred; exact hv0 hred
  have hline := nbLat_eq_of_line hcv.1 hv ha0 hred
  have he : imgLat g = imgLat (c.1.g p) := by rw [hLv, hline, NbCert.imgLat_eq_nbLat hcv]
  obtain ⟨U, hU⟩ := exists_gl_of_imgLat_eq hg he
  refine ⟨c, hc, IsometricGL.symm (show IntEquiv Q' c.2 from ⟨U, fun x => ?_⟩)⟩
  have e1 := NbCert.evalIn_eq hcv (cv x)
  rw [hU, ← mulVec_mulVec, cv_mulVec, ← hQ', evalIn_cv, evalIn_cv] at e1
  exact_mod_cast e1.symm

/-- **Closure under neighbour steps:** if every $p$-neighbour form of every $s \in S$ is equivalent to a member of $S$,
then every form reachable (`NbrReach`) from a form equivalent to a member of $S$ is equivalent to a member of $S$. -/
theorem exists_intEquiv_of_reach {p : ℕ} (S : List (QuadForm ℤ n))
    (hclosed : ∀ s ∈ S, ∀ Q', IsNbrForm p s Q' → ∃ s' ∈ S, IntEquiv s' Q')
    {Q₀ Q : QuadForm ℤ n} (h₀ : ∃ s ∈ S, IntEquiv s Q₀) (hr : NbrReach p Q₀ Q) : ∃ s ∈ S, IntEquiv s Q := by
  induction hr with
  | refl => exact h₀
  | tail _ hstep ih =>
    obtain ⟨s, hs, hsA⟩ := ih
    obtain ⟨Q', hQ', hQ'B⟩ := hstep
    obtain ⟨s', hs', hs'Q'⟩ := hclosed s hs Q' (hQ'.of_intEquiv hsA)
    exact ⟨s', hs', IsometricGL.trans hs'Q' hQ'B⟩

/-- **The closure completeness criterion** (Kneser 1957; Scharlau–Hemkemeier 1998, §2): if the genus of $Q$ is
`KneserConnected` at $p$ and the list $S$ (containing a form equivalent to $Q$) is closed under $p$-neighbour steps, then
every form in the genus of $Q$ is equivalent to a member of $S$. -/
@[kb "kneser1957" "§2 [unverified]"]
theorem exists_intEquiv_of_closed {p : ℕ} {Q : QuadForm ℤ n} (hK : KneserConnected p Q) (S : List (QuadForm ℤ n))
    (hQ : ∃ s ∈ S, IntEquiv s Q)
    (hclosed : ∀ s ∈ S, ∀ Q', IsNbrForm p s Q' → ∃ s' ∈ S, IntEquiv s' Q')
    {Q' : QuadForm ℤ n} (h : SameGenus Q Q') : ∃ s ∈ S, IntEquiv s Q' :=
  exists_intEquiv_of_reach S hclosed hQ (hK Q' h)

end QuadFormsKB.Siegel.Kneser
