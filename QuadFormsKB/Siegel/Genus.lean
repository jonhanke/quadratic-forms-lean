/-
# Siegel's formula: genus, classes, automorphisms, representation numbers

**Layer:** integral forms `QuadForm ℤ n` (upper-triangular coefficients $C$, Hessian $H = C + C^{\mathsf T}$;
`Defs/QuadForm.lean`). **Defines** $\mathrm{GL}_n(K)$-equivalence (`IsometricGL`), integral equivalence and classes
(`IntEquiv`, `QClass`, `classOf`), the automorphism group $\mathrm{Aut}(Q) \le \mathrm{GL}_n(\mathbb{Z})$ (`Aut`),
representation numbers $r_Q(m)$ (`repNum`), the genus (`SameGenus`: equivalent over every $\mathbb{Z}_p$ and over
$\mathbb{R}$) and the classes in it (`genusClasses`). **Proves** that equivalence base-changes to every ring
(`IsometricGL.map`; so a class lies in a genus), invariance of $|\mathrm{Aut}|$ and $r_Q(m)$ on classes, the bridges to
the AWS notes' Hessian notions (`intEquiv_iff_equivZ`, `coe_aut_eq_autZ`), and for positive definite $Q$
(`IntQF.PosDef`): definiteness over $\mathbb{R}$, nondegeneracy, and finiteness of $r_Q(m)$ and of $\mathrm{Aut}(Q)$.

**Conventions:** our own small definitions (Tau Ceti's `IntegralLattice` API is related
work, not imported); **$\mathrm{GL}_n(\mathbb{Z})$-classes** and $\mathrm{Aut} \subseteq \mathrm{GL}_n(\mathbb{Z})$ throughout.
-/
import QuadFormsKB.Literature.Universal.Basic
import QuadFormsKB.Literature.AWS.Measures
import QuadFormsKB.LocalDensity.LowerBounds

open Matrix

namespace QuadFormsKB.Siegel

variable {n : ℕ}

section General

variable {K : Type*} [CommRing K]

/-- **$\mathrm{GL}_n(K)$-equivalence of forms over a commutative ring $K$:** there is an invertible
$g \in \mathrm{GL}_n(K)$ with
$$Q(g\vec{x}) = Q'(\vec{x}) \quad \text{for all } \vec{x} \in K^n.$$
Both forms have coefficients in $K$ and the change of variables is over $K$. Used at $K = \mathbb{Z}$
(`IntEquiv`), $K = \mathbb{Z}_p$ and $K = \mathbb{R}$ (`SameGenus`).

*Relation to the repo:* for a form over $K$ itself this is `QuadForm.IsometricIn K`
(`isometricGL_iff_isometricIn`); the $\mathrm{GL}$ form is used so that `aut` is a subgroup. -/
def IsometricGL (Q Q' : QuadForm K n) : Prop :=
  ∃ g : GL (Fin n) K, ∀ x, Q.eval (g.val *ᵥ x) = Q'.eval x

/-- $Q \sim Q$ (take $g = 1$). -/
theorem IsometricGL.refl (Q : QuadForm K n) : IsometricGL Q Q := ⟨1, fun x => by simp⟩

/-- If $Q(g\vec{x}) = Q'(\vec{x})$ then $Q'(g^{-1}\vec{x}) = Q(\vec{x})$. -/
theorem IsometricGL.symm {Q Q' : QuadForm K n} (h : IsometricGL Q Q') : IsometricGL Q' Q := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, fun x => ?_⟩
  rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- Equivalences compose: $Q(gg'\vec{x}) = Q'(g'\vec{x}) = Q''(\vec{x})$. -/
theorem IsometricGL.trans {Q Q' Q'' : QuadForm K n} (h : IsometricGL Q Q') (h' : IsometricGL Q' Q'') :
    IsometricGL Q Q'' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g * g', fun x => by rw [Units.val_mul, ← mulVec_mulVec, hg, hg']⟩

/-- **Bridge:** `IsometricGL` is the repo's `QuadForm.IsometricIn K` for forms over $K$ (an invertible
matrix is a unit of the matrix ring iff its determinant is a unit). -/
theorem isometricGL_iff_isometricIn (Q Q' : QuadForm K n) :
    IsometricGL Q Q' ↔ Q.IsometricIn K Q' := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, hg⟩
  · rintro ⟨P, hP, h⟩
    exact ⟨Matrix.nonsingInvUnit P hP, h⟩

/-- **The automorphism group** $\mathrm{Aut}_K(Q) = \{g \in \mathrm{GL}_n(K) : Q(g\vec{x}) = Q(\vec{x})
\ \forall \vec{x} \in K^n\}$ of a form over a commutative ring $K$, as a subgroup of $\mathrm{GL}_n(K)$.
At $K = \mathbb{Z}$ this is `Aut`. -/
def aut (Q : QuadForm K n) : Subgroup (GL (Fin n) K) where
  carrier := {g | ∀ x, Q.eval (g.val *ᵥ x) = Q.eval x}
  mul_mem' := by
    intro a b ha hb x
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [Units.val_mul, ← mulVec_mulVec, ha, hb]
  one_mem' := fun x => by simp
  inv_mem' := by
    intro a ha x
    simp only [Set.mem_ofPred_eq] at ha
    rw [← ha, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

end General

/-! ### Values determine the symmetrization -/

/-- $\vec{x}^{\mathsf T} A^{\mathsf T} \vec{x} = \vec{x}^{\mathsf T} A \vec{x}$. -/
theorem dotProduct_mulVec_transpose_self {K : Type*} [CommRing K] (A : Matrix (Fin n) (Fin n) K)
    (x : Fin n → K) : x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]

/-- **An integer matrix $N$ has $\vec{x}^{\mathsf T} N \vec{x} = 0$ for all $\vec{x} \in \mathbb{Z}^n$ iff
$N + N^{\mathsf T} = 0$** (test on $\vec{e}_i$ and $\vec{e}_i + \vec{e}_j$; conversely cancel $2$ in $\mathbb{Z}$). -/
theorem forall_dotProduct_eq_zero_iff (N : Matrix (Fin n) (Fin n) ℤ) :
    (∀ x, x ⬝ᵥ (N *ᵥ x) = 0) ↔ N + Nᵀ = 0 := by
  constructor
  · intro h
    have hd : ∀ i, N i i = 0 := fun i => by simpa using h (Pi.single i 1)
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hd]
    · have := h (Pi.single i 1 + Pi.single j 1)
      simp [mulVec_add, hd] at this
      simp only [Matrix.add_apply, transpose_apply, Matrix.zero_apply]
      linarith
  · intro h x
    have h2 : x ⬝ᵥ ((N + Nᵀ) *ᵥ x) = 2 * (x ⬝ᵥ (N *ᵥ x)) := by
      rw [add_mulVec, dotProduct_add, dotProduct_mulVec_transpose_self]; ring
    rw [h, zero_mulVec, dotProduct_zero] at h2
    linarith

/-- **If $N + N^{\mathsf T} = 0$ over $\mathbb{Z}$, then $\vec{x}^{\mathsf T} f(N) \vec{x} = 0$ for every $\vec{x} \in K^n$**,
for any ring map $f : \mathbb{Z} \to K$, including characteristic $2$: $N = A - A^{\mathsf T}$ with $A$ the
strictly upper part of $N$. -/
theorem dotProduct_map_eq_zero {K : Type*} [CommRing K] (f : ℤ →+* K) (N : Matrix (Fin n) (Fin n) ℤ)
    (h : N + Nᵀ = 0) (x : Fin n → K) : x ⬝ᵥ (N.map f *ᵥ x) = 0 := by
  set A : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => if i < j then N i j else 0
  have hN : N = A - Aᵀ := by
    ext i j
    have hij := congrFun (congrFun h i) j
    have hii := congrFun (congrFun h i) i
    simp only [Matrix.add_apply, transpose_apply, Matrix.zero_apply] at hij hii
    simp only [A, Matrix.sub_apply, transpose_apply, of_apply]
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · simp [hlt, not_lt.mpr hlt.le]
    · simp; linarith
    · simp [hgt, not_lt.mpr hgt.le]; linarith
  rw [hN, Matrix.map_sub _ (map_sub f), sub_mulVec, dotProduct_sub, Matrix.transpose_map,
    dotProduct_mulVec_transpose_self, sub_self]


/-! ### Changes of variables over ℤ and their base change -/

/-- $(g\vec{x})^{\mathsf T} C (g\vec{x}) = \vec{x}^{\mathsf T} (g^{\mathsf T} C g) \vec{x}$. -/
theorem dotProduct_conj {K : Type*} [CommRing K] (g C : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (g *ᵥ x) ⬝ᵥ (C *ᵥ (g *ᵥ x)) = x ⬝ᵥ ((gᵀ * C * g) *ᵥ x) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x gᵀ, vecMul_transpose]

/-- $(f_*Q)(\vec{x}) = \vec{x}^{\mathsf T} f(C) \vec{x}$ for the base change of an integral form along $f : \mathbb{Z} \to K$. -/
theorem eval_map_eq_dotProduct {K : Type*} [CommRing K] (f : ℤ →+* K) (Q : QuadForm ℤ n)
    (x : Fin n → K) : (Q.map f).eval x = x ⬝ᵥ (Q.coeff.map f *ᵥ x) := by
  rw [QuadForm.eval, QuadForm.evalIn_eq_dotProduct]
  simp [QuadForm.map]

/-- **The defect matrix** $N = g^{\mathsf T} C g - C'$ of a change of variables $g$ from $Q$ to $Q'$
($C$, $C'$ the upper-triangular coefficient matrices). $Q(g\vec{x}) - Q'(\vec{x}) = \vec{x}^{\mathsf T} N \vec{x}$. -/
def defect (Q Q' : QuadForm ℤ n) (g : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  gᵀ * Q.coeff * g - Q'.coeff

/-- $(f_*Q)(f(g)\vec{x}) - (f_*Q')(\vec{x}) = \vec{x}^{\mathsf T} f(N) \vec{x}$ with $N$ the `defect`. -/
theorem eval_map_sub_eq {K : Type*} [CommRing K] (f : ℤ →+* K) (Q Q' : QuadForm ℤ n)
    (g : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → K) :
    (Q.map f).eval (g.map f *ᵥ x) - (Q'.map f).eval x = x ⬝ᵥ ((defect Q Q' g).map f *ᵥ x) := by
  rw [eval_map_eq_dotProduct, eval_map_eq_dotProduct, dotProduct_conj, ← dotProduct_sub,
    ← sub_mulVec, defect, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map]

/-- **$Q(g\vec{x}) = Q'(\vec{x})$ on $\mathbb{Z}^n$ iff $N + N^{\mathsf T} = 0$** for the defect $N$. -/
theorem eval_mulVec_eq_iff (Q Q' : QuadForm ℤ n) (g : Matrix (Fin n) (Fin n) ℤ) :
    (∀ x, Q.eval (g *ᵥ x) = Q'.eval x) ↔ defect Q Q' g + (defect Q Q' g)ᵀ = 0 := by
  have key : ∀ x : Fin n → ℤ, Q.eval (g *ᵥ x) - Q'.eval x = x ⬝ᵥ (defect Q Q' g *ᵥ x) := by
    intro x
    have := eval_map_sub_eq (RingHom.id ℤ) Q Q' g x
    simpa [QuadForm.map] using this
  rw [← forall_dotProduct_eq_zero_iff]
  refine forall_congr' fun x => ?_
  rw [← key, sub_eq_zero]

/-- **An identity $Q(g\vec{x}) = Q'(\vec{x})$ on $\mathbb{Z}^n$ holds after any base change** $f : \mathbb{Z} \to K$,
for all $\vec{x} \in K^n$ (also in characteristic $2$, e.g. $K = \mathbb{Z}_2$). -/
theorem eval_mulVec_map {K : Type*} [CommRing K] (f : ℤ →+* K) {Q Q' : QuadForm ℤ n}
    {g : Matrix (Fin n) (Fin n) ℤ} (h : ∀ x, Q.eval (g *ᵥ x) = Q'.eval x) (x : Fin n → K) :
    (Q.map f).eval (g.map f *ᵥ x) = (Q'.map f).eval x := by
  rw [← sub_eq_zero, eval_map_sub_eq]
  exact dotProduct_map_eq_zero f _ ((eval_mulVec_eq_iff Q Q' g).mp h) x

/-- **$\mathbb{Z}$-equivalence implies $K$-equivalence** for every ring $K$ (e.g. $\mathbb{Z}_p$, $\mathbb{R}$). -/
theorem IsometricGL.map {K : Type*} [CommRing K] (f : ℤ →+* K) {Q Q' : QuadForm ℤ n}
    (h : IsometricGL Q Q') : IsometricGL (Q.map f) (Q'.map f) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨Units.map (RingHom.mapMatrix (m := Fin n) f).toMonoidHom g, fun x => ?_⟩
  have e : ((Units.map (RingHom.mapMatrix (m := Fin n) f).toMonoidHom g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = g.val.map f := rfl
  rw [e]
  exact eval_mulVec_map f hg x

/-- **Hessian form:** $Q(g\vec{x}) = Q'(\vec{x})$ for all $\vec{x} \in \mathbb{Z}^n$ iff $g^{\mathsf T} H g = H'$,
where $H = C + C^{\mathsf T}$, $H' = C' + C'^{\mathsf T}$ are the Hessians (`QuadForm.hessian`). -/
theorem eval_mulVec_eq_iff_hessian (Q Q' : QuadForm ℤ n) (g : Matrix (Fin n) (Fin n) ℤ) :
    (∀ x, Q.eval (g *ᵥ x) = Q'.eval x) ↔ gᵀ * Q.hessian * g = Q'.hessian := by
  rw [eval_mulVec_eq_iff, defect, QuadForm.hessian, QuadForm.hessian]
  constructor <;> intro h
  · rw [← sub_eq_zero, ← h]
    simp only [transpose_sub, transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
    abel
  · rw [← sub_eq_zero] at h
    rw [← h]
    simp only [transpose_sub, transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
    abel


/-! ### Integral equivalence, classes, automorphisms -/

/-- **Integral equivalence ($\mathrm{GL}_n(\mathbb{Z})$-equivalence)** of integral forms: $Q(g\vec{x}) = Q'(\vec{x})$
for all $\vec{x} \in \mathbb{Z}^n$, for some $g \in \mathrm{GL}_n(\mathbb{Z})$ ($\det g = \pm 1$).

*Convention:* classes are **$\mathrm{GL}_n(\mathbb{Z})$-classes**, not proper
($\mathrm{SL}_n(\mathbb{Z})$) classes, throughout the Siegel files.

*See also:* `intEquiv_iff_equivZ` (the AWS notes' `EquivZ` on Hessians), `IntEquiv.sameGenus`. -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 [unverified]"]
def IntEquiv (Q Q' : QuadForm ℤ n) : Prop := IsometricGL Q Q'

/-- `IntEquiv` as a setoid on integral forms in $n$ variables. -/
def intSetoid (n : ℕ) : Setoid (QuadForm ℤ n) where
  r := IntEquiv
  iseqv := ⟨IsometricGL.refl, IsometricGL.symm, IsometricGL.trans⟩

/-- **Classes** of integral forms in $n$ variables: the quotient by $\mathrm{GL}_n(\mathbb{Z})$-equivalence. -/
abbrev QClass (n : ℕ) := Quotient (intSetoid n)

/-- **The class** $[Q]$ of an integral form. -/
def classOf (Q : QuadForm ℤ n) : QClass n := Quotient.mk (intSetoid n) Q

/-- $[Q] = [Q']$ iff $Q \sim_{\mathbb{Z}} Q'$. -/
theorem classOf_eq_classOf_iff {Q Q' : QuadForm ℤ n} : classOf Q = classOf Q' ↔ IntEquiv Q Q' :=
  Quotient.eq (r := intSetoid n)

/-- **The integral automorphism group** $\mathrm{Aut}(Q) = O(Q)(\mathbb{Z}) = \{g \in \mathrm{GL}_n(\mathbb{Z}) :
Q(g\vec{x}) = Q(\vec{x})\ \forall \vec{x} \in \mathbb{Z}^n\}$, a subgroup of $\mathrm{GL}_n(\mathbb{Z})$
(including improper automorphisms, $\det g = -1$). Finite for positive definite $Q$
(`IntQF.PosDef.finite_aut`). Hanke 2004 writes $|\mathrm{Aut}(Q')|$ in (4.5), p. 366.

*Bridge:* `coe_aut_eq_autZ` (the AWS notes' `autZ` on the Hessian). -/
@[kb "hanke2004" "(4.5), p. 366 (|Aut(Q')|)"]
abbrev Aut (Q : QuadForm ℤ n) : Subgroup (GL (Fin n) ℤ) := aut Q

/-- **Bridge to `AWS.EquivZ`:** $Q \sim_{\mathbb{Z}} Q'$ iff some $X \in \mathrm{GL}_n(\mathbb{Z})$ has
$X^{\mathsf T} H_Q X = H_{Q'}$, i.e. `AWS.EquivZ` $H_{Q'}$ $H_Q$ (note the order of the arguments there). -/
theorem intEquiv_iff_equivZ (Q Q' : QuadForm ℤ n) :
    IntEquiv Q Q' ↔ AWS.EquivZ Q'.hessian Q.hessian := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (eval_mulVec_eq_iff_hessian Q Q' g.val).mp hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (eval_mulVec_eq_iff_hessian Q Q' g.val).mpr hg⟩

/-- **Bridge to `AWS.autZ`:** $\mathrm{Aut}(Q)$ is the AWS notes' $\{X \in \mathrm{GL}_n(\mathbb{Z}) : X^{\mathsf T}HX = H\}$. -/
theorem coe_aut_eq_autZ (Q : QuadForm ℤ n) : ((Aut Q : Set (GL (Fin n) ℤ))) = AWS.autZ Q.hessian := by
  ext g
  exact eval_mulVec_eq_iff_hessian Q Q g.val

/-- **Conjugation** $h \mapsto g h g^{-1}$ identifies $\mathrm{Aut}(Q')$ with $\mathrm{Aut}(Q)$ when $Q(g\vec{x}) = Q'(\vec{x})$. -/
def autEquivOfIsometry {Q Q' : QuadForm ℤ n} (g : GL (Fin n) ℤ)
    (hg : ∀ x, Q.eval (g.val *ᵥ x) = Q'.eval x) : Aut Q' ≃ Aut Q where
  toFun h := ⟨g * h.1 * g⁻¹, fun x => by
    have hh := h.2
    have hinv : ∀ y, Q.eval y = Q'.eval ((g⁻¹).val *ᵥ y) := fun y => by
      rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    simp only [Units.val_mul, ← mulVec_mulVec]
    rw [hg, hh (((g⁻¹).val *ᵥ x)), hinv x]⟩
  invFun h := ⟨g⁻¹ * h.1 * g, fun x => by
    have hh := h.2
    simp only [Units.val_mul, ← mulVec_mulVec]
    rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec,
      hh (g.val *ᵥ x), hg]⟩
  left_inv h := by ext1; simp [mul_assoc]
  right_inv h := by ext1; simp [mul_assoc]

/-- $|\mathrm{Aut}(Q)|$ is a class invariant (as `Nat.card`, which is $0$ for an infinite group). -/
theorem card_aut_eq_of_intEquiv {Q Q' : QuadForm ℤ n} (h : IntEquiv Q Q') :
    Nat.card (Aut Q) = Nat.card (Aut Q') := by
  obtain ⟨g, hg⟩ := h
  exact (Nat.card_congr (autEquivOfIsometry g hg)).symm

/-! ### Representation numbers -/

/-- **The representations of $m$ by $Q$:** $\{\vec{x} \in \mathbb{Z}^n : Q(\vec{x}) = m\}$ (integer vectors). -/
def repSet (Q : QuadForm ℤ n) (m : ℤ) : Set (Fin n → ℤ) := {x | Q.eval x = m}

/-- **The representation number** $r_Q(m) = \#\{\vec{x} \in \mathbb{Z}^n : Q(\vec{x}) = m\}$, as `Nat.card`
(so it is $0$ if the set is infinite; for positive definite $Q$ it is finite, `IntQF.PosDef.repSet_finite`).
For the sum of four squares it is the AWS notes' `r4` (`repNum_Q4`). -/
@[kb "hanke2004" "§2, r_Q(m) = #R_Q(m), p. 357"]
noncomputable def repNum (Q : QuadForm ℤ n) (m : ℤ) : ℕ := Nat.card (repSet Q m)

/-- $r_Q(m)$ is a class invariant: $\vec{x} \mapsto g^{-1}\vec{x}$ is a bijection of representations. -/
theorem repNum_eq_of_intEquiv {Q Q' : QuadForm ℤ n} (h : IntEquiv Q Q') (m : ℤ) :
    repNum Q m = repNum Q' m := by
  obtain ⟨g, hg⟩ := h
  have hinv : ∀ y, Q.eval y = Q'.eval ((g⁻¹).val *ᵥ y) := fun y => by
    rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine Nat.card_congr
    { toFun := fun x => ⟨(g⁻¹).val *ᵥ x.1, by
        have := x.2; simp only [repSet, Set.mem_ofPred_eq] at this ⊢; rw [← hinv, this]⟩
      invFun := fun y => ⟨g.val *ᵥ y.1, by
        have := y.2; simp only [repSet, Set.mem_ofPred_eq] at this ⊢; rw [hg, this]⟩
      left_inv := fun x => by
        ext1; simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      right_inv := fun y => by
        ext1; simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] }

/-- $|\mathrm{Aut}(Q')|$ as a function of the class $[Q']$ (well defined by `card_aut_eq_of_intEquiv`). -/
noncomputable def QClass.autCard (c : QClass n) : ℕ :=
  Quotient.lift (s := intSetoid n) (fun Q => Nat.card (Aut Q)) (fun _ _ h => card_aut_eq_of_intEquiv h) c

/-- $r_{Q'}(m)$ as a function of the class $[Q']$ (well defined by `repNum_eq_of_intEquiv`). -/
noncomputable def QClass.repNum (c : QClass n) (m : ℤ) : ℕ :=
  Quotient.lift (s := intSetoid n) (fun Q => _root_.QuadFormsKB.Siegel.repNum Q m) (fun _ _ h => repNum_eq_of_intEquiv h m) c

@[simp] theorem QClass.autCard_classOf (Q : QuadForm ℤ n) : (classOf Q).autCard = Nat.card (Aut Q) := rfl

@[simp] theorem QClass.repNum_classOf (Q : QuadForm ℤ n) (m : ℤ) :
    (classOf Q).repNum m = _root_.QuadFormsKB.Siegel.repNum Q m := rfl

/-! ### The genus -/

/-- **Same genus:** $Q$ and $Q'$ are equivalent over $\mathbb{Z}_p$ for every prime $p$ and over $\mathbb{R}$:
$$\forall p\ \exists g_p \in \mathrm{GL}_n(\mathbb{Z}_p):\ Q(g_p\vec{x}) = Q'(\vec{x})\ (\vec{x} \in \mathbb{Z}_p^n),
\qquad \exists g_\infty \in \mathrm{GL}_n(\mathbb{R}):\ Q(g_\infty\vec{x}) = Q'(\vec{x})\ (\vec{x} \in \mathbb{R}^n).$$
The forms are base-changed coefficientwise (`QuadForm.map (Int.castRingHom ℤ_[p])`), so at $p = 2$ this is
equivalence of the integral forms (not of their Gram matrices).

*Conventions:* $\mathrm{GL}$ (not $\mathrm{SL}$) at every place. Equivalent formulations (local lattices,
double cosets) are in `Literature/AWS/Adelic.lean` (`latGenus`); a bridge is a follow-up.

*See also:* `IntEquiv.sameGenus`, `genusClasses`. -/
@[kb "cassels1978" "Ch. 9, §1, genus, p. 128 [unverified]"]
def SameGenus (Q Q' : QuadForm ℤ n) : Prop :=
  (∀ (p : ℕ) [Fact p.Prime],
      IsometricGL (Q.map (Int.castRingHom ℤ_[p])) (Q'.map (Int.castRingHom ℤ_[p]))) ∧
    IsometricGL (Q.map (Int.castRingHom ℝ)) (Q'.map (Int.castRingHom ℝ))

/-- Same genus is reflexive. -/
theorem SameGenus.refl (Q : QuadForm ℤ n) : SameGenus Q Q :=
  ⟨fun _ _ => IsometricGL.refl _, IsometricGL.refl _⟩

/-- Same genus is symmetric. -/
theorem SameGenus.symm {Q Q' : QuadForm ℤ n} (h : SameGenus Q Q') : SameGenus Q' Q :=
  ⟨fun p _ => (h.1 p).symm, h.2.symm⟩

/-- Same genus is transitive. -/
theorem SameGenus.trans {Q Q' Q'' : QuadForm ℤ n} (h : SameGenus Q Q') (h' : SameGenus Q' Q'') :
    SameGenus Q Q'' :=
  ⟨fun p _ => (h.1 p).trans (h'.1 p), h.2.trans h'.2⟩

/-- **A class lies in one genus:** $\mathbb{Z}$-equivalent forms are in the same genus (`IsometricGL.map`). -/
theorem IntEquiv.sameGenus {Q Q' : QuadForm ℤ n} (h : IntEquiv Q Q') : SameGenus Q Q' :=
  ⟨fun _ _ => IsometricGL.map _ h, IsometricGL.map _ h⟩

/-- **The classes in the genus of $Q$:** $\{[Q'] : Q' \text{ in the genus of } Q\}$ (`SameGenus`), a set of
$\mathrm{GL}_n(\mathbb{Z})$-classes. Its finiteness for positive definite $Q$ (finiteness of the class number) is an
input, `GenusFinite`. -/
@[kb "hanke2004" "(4.5), p. 366 (Gen(Q))"]
def genusClasses (Q : QuadForm ℤ n) : Set (QClass n) := {c | ∃ Q', classOf Q' = c ∧ SameGenus Q Q'}

/-- $[Q'] \in \mathrm{Gen}(Q)$ iff $Q'$ is in the genus of $Q$ (independent of the representative). -/
theorem classOf_mem_genusClasses_iff {Q Q' : QuadForm ℤ n} :
    classOf Q' ∈ genusClasses Q ↔ SameGenus Q Q' := by
  constructor
  · rintro ⟨Q'', h, hg⟩
    exact hg.trans (classOf_eq_classOf_iff.mp h).sameGenus
  · exact fun h => ⟨Q', rfl, h⟩

/-- $[Q] \in \mathrm{Gen}(Q)$. -/
theorem classOf_self_mem_genusClasses (Q : QuadForm ℤ n) : classOf Q ∈ genusClasses Q :=
  classOf_mem_genusClasses_iff.mpr (SameGenus.refl Q)

/-- Forms in the same genus have the same set of classes. -/
theorem genusClasses_eq_of_sameGenus {Q Q' : QuadForm ℤ n} (h : SameGenus Q Q') :
    genusClasses Q = genusClasses Q' := by
  ext c
  induction c using Quotient.inductionOn with
  | h Q'' =>
    change classOf Q'' ∈ _ ↔ classOf Q'' ∈ _
    rw [classOf_mem_genusClasses_iff, classOf_mem_genusClasses_iff]
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩


/-! ### Positive definite forms: real definiteness and finiteness -/

/-- $Q(\vec{x})$ computed in $K$ is the image of $Q(\vec{x}) \in \mathbb{Z}$, for $\vec{x} \in \mathbb{Z}^n$. -/
theorem evalIn_intCast {K : Type*} [CommRing K] (Q : QuadForm ℤ n) (x : Fin n → ℤ) :
    Q.evalIn K (fun i => (x i : K)) = (Q.eval x : K) := by
  have := AWS.evalIn_map Q (Int.castRingHom K) x
  simpa [Function.comp_def] using this.symm

/-- $\vec{x} \mapsto Q(\vec{x})$ is continuous on $\mathbb{R}^n$. -/
theorem continuous_evalIn_real (Q : IntQF n) : Continuous fun x : Fin n → ℝ => Q.evalIn ℝ x := by
  unfold QuadForm.evalIn
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs <;> fun_prop

end QuadFormsKB.Siegel

namespace QuadFormsKB.IntQF.PosDef

open Matrix

variable {n : ℕ}

/-- A positive definite form is $\ge 0$ on $\mathbb{Z}^n$. -/
theorem eval_nonneg {Q : IntQF n} (hQ : Q.PosDef) (x : Fin n → ℤ) : 0 ≤ Q.eval x := by
  by_cases hx : x = 0
  · subst hx; simp [QuadForm.evalIn]
  · exact (hQ x hx).le

/-- A positive definite integral form is $\ge 0$ on $\mathbb{Q}^n$ (clear denominators, homogeneity). -/
theorem evalIn_rat_nonneg {Q : IntQF n} (hQ : Q.PosDef) (y : Fin n → ℚ) :
    0 ≤ Q.evalIn ℚ y := by
  set d : ℕ := ∏ i, (y i).den
  have hd : (d : ℚ) ≠ 0 := by
    simp only [d, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (y i).den_nz
  set x : Fin n → ℤ := fun i => (y i).num * ((d / (y i).den : ℕ) : ℤ)
  have hx : (fun i => (x i : ℚ)) = (d : ℚ) • y := by
    funext i
    have hdvd : (y i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    simp only [x, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div hdvd (by exact_mod_cast (y i).den_nz)]
    conv_rhs => rw [← Rat.num_div_den (y i)]
    field_simp
  have h1 := Siegel.evalIn_intCast (K := ℚ) Q x
  rw [hx, LocalDensity.evalIn_smul] at h1
  have h2 : (0 : ℚ) ≤ (Q.eval x : ℚ) := by exact_mod_cast hQ.eval_nonneg x
  rw [← h1] at h2
  have h3 : (0 : ℚ) < (d : ℚ) ^ 2 := by positivity
  exact nonneg_of_mul_nonneg_right (by linarith) h3

/-- A positive definite integral form is $\ge 0$ on $\mathbb{R}^n$ (density of $\mathbb{Q}^n$, continuity). -/
theorem evalIn_real_nonneg {Q : IntQF n} (hQ : Q.PosDef) (y : Fin n → ℝ) :
    0 ≤ Q.evalIn ℝ y := by
  have hd : DenseRange (Pi.map fun (_ : Fin n) (q : ℚ) => (q : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun y => 0 ≤ Q.evalIn ℝ y) y
    (isClosed_le continuous_const (Siegel.continuous_evalIn_real Q)) fun q => ?_
  have := AWS.evalIn_map Q (Rat.castHom ℝ) q
  have e : (Pi.map fun (_ : Fin n) (q : ℚ) => (q : ℝ)) q = (Rat.castHom ℝ) ∘ q := rfl
  rw [e, ← this]
  exact Rat.cast_nonneg.mpr (evalIn_rat_nonneg hQ q)

/-- **Positive definite integral forms are nondegenerate** ($\det H \ne 0$): a nonzero integer kernel vector
$\vec{v}$ of $H$ would give $2Q(\vec{v}) = \vec{v}^{\mathsf T}H\vec{v} = 0$. -/
theorem nondegenerate {Q : IntQF n} (hQ : Q.PosDef) : Q.Nondegenerate := by
  intro hdet
  obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h2 := LocalDensity.two_mul_eval_eq_hessian Q v
  rw [hHv, dotProduct_zero] at h2
  have := hQ v hv
  omega

/-- **Positive definite over $\mathbb{Z}$ implies positive definite over $\mathbb{R}$:** $Q(\vec{x}) > 0$ for every
nonzero $\vec{x} \in \mathbb{R}^n$. (This settles the parenthetical remark in `IntQF.PosDef`.) *Proof:* $Q \ge 0$ on
$\mathbb{R}^n$; a real zero $\vec{x} \ne 0$ of a semidefinite form lies in the kernel of $H$, so $\det H = 0$,
contradicting `nondegenerate`. -/
@[kb "cassels1978" "Ch. 9 [unverified]"]
theorem evalIn_real_pos {Q : IntQF n} (hQ : Q.PosDef) (x : Fin n → ℝ) (hx : x ≠ 0) :
    0 < Q.evalIn ℝ x := by
  rcases (hQ.evalIn_real_nonneg x).lt_or_eq with h | h
  · exact h
  exfalso
  set Hr := Q.hessian.map (algebraMap ℤ ℝ)
  have hB : ∀ w, x ⬝ᵥ (Hr *ᵥ w) = 0 := by
    intro w
    set B := x ⬝ᵥ (Hr *ᵥ w)
    set c := Q.evalIn ℝ w
    have hc : 0 ≤ c := hQ.evalIn_real_nonneg w
    have key : ∀ t : ℝ, 0 ≤ t * B + t ^ 2 * c := by
      intro t
      have hp := QuadForm.polar_eq_hessian ℝ Q x (t • w)
      rw [LocalDensity.evalIn_smul, ← h, mulVec_smul, dotProduct_smul, smul_eq_mul] at hp
      have := hQ.evalIn_real_nonneg (x + t • w)
      linarith
    have := key (-B / (c + 1))
    have hc1 : 0 < c + 1 := by linarith
    rw [div_pow, neg_sq] at this
    have h' : 0 ≤ -B ^ 2 / (c + 1) ^ 2 := by
      have e : -B / (c + 1) * B + B ^ 2 / (c + 1) ^ 2 * c = -B ^ 2 / (c + 1) ^ 2 := by
        field_simp; ring
      linarith
    have : B ^ 2 ≤ 0 := by
      have := div_nonneg_iff.mp h'
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · nlinarith [sq_nonneg (c + 1)]
    nlinarith [sq_nonneg B]
  have hvec : x ᵥ* Hr = 0 := by
    funext j
    have := hB (Pi.single j 1)
    rw [dotProduct_mulVec] at this
    simpa using this
  have hdetr : Hr.det = 0 := Matrix.exists_vecMul_eq_zero_iff.mp ⟨x, hx, hvec⟩
  have : ((Q.hessian.det : ℤ) : ℝ) = 0 := by
    rw [← hdetr]
    exact RingHom.map_det (algebraMap ℤ ℝ) Q.hessian
  exact hQ.nondegenerate (by exact_mod_cast this)

/-- **Coercivity:** there is $c > 0$ with $Q(\vec{x}) \ge c\,\|\vec{x}\|^2$ on $\mathbb{R}^n$ (sup norm; $c$ is the
minimum of $Q$ on the unit sphere). -/
theorem exists_coercive {Q : IntQF n} (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * ‖x‖ ^ 2 ≤ Q.evalIn ℝ x := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp [QuadForm.evalIn]
  · have hS : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hS
      (Siegel.continuous_evalIn_real Q).continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl; simp at hu
    refine ⟨Q.evalIn ℝ u, hQ.evalIn_real_pos u hu0, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [QuadForm.evalIn]
    · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
        simp [norm_smul, hnx.ne']
      have h1 := hmin hmem
      simp only [Set.mem_ofPred_eq] at h1
      rw [LocalDensity.evalIn_smul] at h1
      have h2 : ‖x‖⁻¹ ^ 2 = (‖x‖ ^ 2)⁻¹ := by rw [inv_pow]
      rw [h2] at h1
      have h3 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      rw [inv_mul_eq_div, le_div_iff₀ h3] at h1
      linarith

/-- **Finitely many integer vectors of bounded value:** $\{\vec{x} \in \mathbb{Z}^n : Q(\vec{x}) \le M\}$ is finite. -/
theorem finite_setOf_eval_le {Q : IntQF n} (hQ : Q.PosDef) (M : ℤ) :
    {x : Fin n → ℤ | Q.eval x ≤ M}.Finite := by
  obtain ⟨c, hc, hco⟩ := hQ.exists_coercive
  set R : ℝ := max 1 (M / c)
  refine (Set.Finite.pi' (t := fun _ : Fin n => Set.Icc (-⌈R⌉) ⌈R⌉)
    fun _ => Set.finite_Icc _ _).subset fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hle : ‖(fun i => (x i : ℝ))‖ ≤ R := by
    have h1 := hco (fun i => (x i : ℝ))
    rw [Siegel.evalIn_intCast] at h1
    have hM : ((Q.eval x : ℤ) : ℝ) ≤ M := by exact_mod_cast hx
    by_cases h : ‖(fun i => (x i : ℝ))‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · push Not at h
      refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hc]
      nlinarith [mul_pos (mul_pos hc (lt_trans one_pos h)) (sub_pos.mpr h)]
  intro i
  have hi : |(x i : ℝ)| ≤ R := by
    have := norm_le_pi_norm (fun i => (x i : ℝ)) i
    rw [Real.norm_eq_abs] at this
    linarith
  have hR := Int.le_ceil R
  rw [abs_le] at hi
  constructor
  · have : (-(⌈R⌉ : ℝ)) ≤ (x i : ℝ) := by linarith
    exact_mod_cast this
  · have : (x i : ℝ) ≤ (⌈R⌉ : ℝ) := by linarith
    exact_mod_cast this

/-- **$r_Q(m)$ is finite** for positive definite $Q$: $\{\vec{x} \in \mathbb{Z}^n : Q(\vec{x}) = m\}$ is finite. -/
@[kb "cassels1978" "Ch. 9 [unverified]"]
theorem repSet_finite {Q : IntQF n} (hQ : Q.PosDef) (m : ℤ) : (Siegel.repSet Q m).Finite :=
  (hQ.finite_setOf_eval_le m).subset fun _ hx => le_of_eq hx

/-- **$\mathrm{Aut}(Q)$ is finite** for positive definite $Q$: the $j$-th column of $g \in \mathrm{Aut}(Q)$ represents
$Q(\vec{e}_j)$, and there are finitely many such vectors. -/
@[kb "cassels1978" "Ch. 9, Lemma on finiteness of O(f) [unverified]"]
theorem finite_aut {Q : IntQF n} (hQ : Q.PosDef) : Finite (Siegel.Aut Q) := by
  set t : Fin n → Set (Fin n → ℤ) := fun j => Siegel.repSet Q (Q.eval (Pi.single j 1))
  have ht : {f : Fin n → Fin n → ℤ | ∀ j, f j ∈ t j}.Finite :=
    Set.Finite.pi' fun j => hQ.repSet_finite _
  have := ht.to_subtype
  refine Finite.of_injective (β := {f : Fin n → Fin n → ℤ | ∀ j, f j ∈ t j})
    (fun g => ⟨fun j => g.1.val *ᵥ Pi.single j 1, fun j => g.2 _⟩) ?_
  intro g h hgh
  have hgh' := congrArg Subtype.val hgh
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := congrFun (congrFun hgh' j) i
  simpa [mulVec_single_one] using this

/-- $|\mathrm{Aut}(Q)| \ge 1$ for positive definite $Q$. -/
theorem card_aut_pos {Q : IntQF n} (hQ : Q.PosDef) : 0 < Nat.card (Siegel.Aut Q) := by
  have := hQ.finite_aut
  exact Nat.card_pos

end QuadFormsKB.IntQF.PosDef
