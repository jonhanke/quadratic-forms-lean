/-
# Cassels, Chapter 10, Theorem 3.1: the even Clifford group maps onto the rotations

**Setting.** O'Meara's abstract quadratic spaces (`QuadFormsKB.OMeara`): a field $k$ of characteristic $\ne 2$, a
finite-dimensional regular quadratic space $(V, Q)$ (`(QuadraticMap.associated Q).Nondegenerate`), the orthogonal group
$O(V)$ = `orth Q`, the rotations $O^+(V)$ = `orthPlus Q`, symmetries $\tau_{\vec y}$ = `symmetry Q y hy`. From
`Ch10/Clifford.lean`: the Clifford group `cliffordGroup Q` (units $u$ of $C(V)$ with $uVu^{-1} = V$), its even part
$M_0(V)$ = `M0 Q`, and $T_u\vec x = u\vec x u^{-1}$ = `conjHom u`.

**Proves** Cassels, Ch. 10, Theorem 3.1 (p. 176):
* `range_conjM0`: the image of $u \mapsto T_u$ on $M_0(V)$ is exactly $O^+(V)$;
* `conjM0_eq_one_iff`: $T_u = 1$ if and only if $u \in k$ (the kernel is $k^\times$).

**Proof notes.** By Cassels (3.2), $T_{\vec y} = -\tau_{\vec y}$, so $T_{\vec y_1 \cdots \vec y_r} =
(-1)^r\tau_{\vec y_1}\cdots\tau_{\vec y_r}$ (`conjHom_vecProd`). A rotation is a product of an even number of symmetries
(Cartan–Dieudonné, O'Meara 43:3, `exists_symmetry_prod_eq_length_le`), which gives surjectivity. Conversely, if
$T_u$ for even $u$ were a product of an odd number $r$ of symmetries, then $v = (\vec y_1\cdots\vec y_r)^{-1}u$ would be an
odd unit anticommuting with $V$, which is impossible (`eq_zero_of_odd_anticomm`). Checked against the printed page (p. 176) on 2026-10-27: the same
statement (Cassels states that $u \mapsto T_u$ is an isomorphism $M_0(V)/k^* \to O^+$; here it is split into the image
and the kernel).
-/
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.Cassels.Ch10.Clifford

open Module CliffordAlgebra

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

section SpinOrth

open QuadFormsKB.OMeara

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V}

/-- The product $\tau_{\vec y_1}\cdots\tau_{\vec y_r}$ of symmetries. -/
noncomputable def symProd (l : List V) (hl : ∀ y ∈ l, Q y ≠ 0) : V ≃ₗ[k] V :=
  (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod

theorem symProd_cons (y : V) (l : List V) (hl : ∀ z ∈ y :: l, Q z ≠ 0) :
    symProd (y :: l) hl = symmetry Q y (hl y (List.mem_cons_self ..)) *
      symProd l (fun z hz => hl z (List.mem_cons_of_mem y hz)) := by
  simp only [symProd, List.attach_cons, List.map_cons, List.prod_cons, List.map_map]
  rfl

theorem det_symProd (l : List V) (hl : ∀ y ∈ l, Q y ≠ 0) :
    LinearEquiv.det (symProd l hl) = (-1 : kˣ) ^ l.length := by
  induction l with
  | nil => simp [symProd]
  | cons y l ih => rw [symProd_cons, map_mul, ih, det_symmetry, List.length_cons, pow_succ']

theorem polar_eq_two_mul_bil (x y : V) : QuadraticMap.polar Q x y = 2 * bil Q x y := by
  have := congrArg (fun B : LinearMap.BilinForm k V => B x y)
    (QuadraticMap.two_nsmul_associated (S := k) (Q := Q))
  simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply] at this
  rw [← this, bil, two_nsmul, two_mul]

theorem negE_mul_comm (σ : V ≃ₗ[k] V) : LinearEquiv.neg k * σ = σ * LinearEquiv.neg k := by
  ext x; simp

theorem negE_sq : (LinearEquiv.neg k : V ≃ₗ[k] V) ^ 2 = 1 := by
  ext x; simp [sq]

/-- $T_{\vec y} = -\tau_{\vec y}$ (Cassels (3.2)). -/
theorem conjHom_vecUnit_eq (y : V) (hy : Q y ≠ 0) :
    conjHom ⟨vecUnit y hy, vecUnit_mem y hy⟩ = LinearEquiv.neg k * symmetry Q y hy := by
  ext x
  rw [conjHom_vecUnit, LinearEquiv.mul_apply, LinearEquiv.neg_apply, symmetry_apply, polar_eq_two_mul_bil]

theorem conjHom_vecProd (l : List V) (hl : ∀ y ∈ l, Q y ≠ 0) :
    conjHom (vecProd l hl) = LinearEquiv.neg k ^ l.length * symProd l hl := by
  induction l with
  | nil => simp [vecProd, symProd]
  | cons y l ih =>
    rw [vecProd_cons, map_mul, ih, conjHom_vecUnit_eq, symProd_cons, List.length_cons, pow_succ']
    have hc : Commute (symmetry Q y (hl y (List.mem_cons_self ..))) (LinearEquiv.neg k ^ l.length) :=
      (Commute.pow_right (negE_mul_comm _).symm _)
    rw [mul_assoc, ← mul_assoc (symmetry Q y _), hc.eq, mul_assoc, mul_assoc]

theorem neg_one_units_ne_one : (-1 : kˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : kˣ => (u : k)) h
  simp only [Units.val_neg, Units.val_one] at this
  have h2 : (2 : k) = 0 := by linear_combination -this
  exact Invertible.ne_zero (2 : k) h2

theorem even_length_of_det (l : List V) (hl : ∀ y ∈ l, Q y ≠ 0)
    (h : LinearEquiv.det (symProd l hl) = 1) : Even l.length := by
  rw [det_symProd] at h
  exact (neg_one_pow_eq_one_iff_even neg_one_units_ne_one).1 h

theorem negE_pow_even {r : ℕ} (hr : Even r) : (LinearEquiv.neg k : V ≃ₗ[k] V) ^ r = 1 := by
  obtain ⟨m, rfl⟩ := hr
  rw [← two_mul, pow_mul, negE_sq, one_pow]

/-- The map $u \mapsto T_u$ on $M_0(V)$. -/
noncomputable def conjM0 : M0 Q →* (V ≃ₗ[k] V) := conjHom.comp (Subgroup.inclusion M0_le)

theorem conjM0_apply (u : M0 Q) : conjM0 u = conjHom (Subgroup.inclusion M0_le u) := rfl

/-- Rotations come from $M_0(V)$: a rotation is $T_{\vec y_1\cdots\vec y_r}$, $r$ even (Cartan–Dieudonné). -/
theorem exists_M0_of_orthPlus (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[k] V}
    (hσ : σ ∈ orthPlus Q) :
    ∃ l : List V, ∃ hl : ∀ y ∈ l, Q y ≠ 0, Even l.length ∧ σ = symProd l hl ∧
      conjHom (vecProd l hl) = σ := by
  obtain ⟨l, hl, hσl, -⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ.1
  have hσl' : σ = symProd l hl := hσl
  have hev : Even l.length := even_length_of_det l hl (by rw [← hσl']; exact hσ.2)
  exact ⟨l, hl, hev, hσl', by rw [conjHom_vecProd, negE_pow_even hev, one_mul, hσl']⟩

theorem vecProd_mem_even {l : List V} (hl : ∀ y ∈ l, Q y ≠ 0) (hev : Even l.length) :
    (((vecProd l hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
  have := vecProd_mem_evenOdd l hl
  rwa [(ZMod.natCast_eq_zero_iff_even).2 hev] at this

/-- **Cassels, Ch. 10, Theorem 3.1, p. 176.** For a regular quadratic space $V$ over a field of characteristic
$\ne 2$, the map $u \mapsto T_u$, $T_u\vec x = u\vec x u^{-1}$, is a homomorphism of $M_0(V)$ onto the group $O^+(V)$
of rotations, with kernel $k^\times$: (i) its image is exactly $O^+(V)$; (ii) $T_u = 1$ if and only if $u \in k$. -/
@[kb "cassels1978" "Ch. 10, Theorem 3.1, p. 176"]
theorem range_conjM0 (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (conjM0 (Q := Q)).range = orthPlus Q := by
  ext σ
  constructor
  · rintro ⟨u, rfl⟩
    have horth : conjM0 u ∈ orth Q := fun x => conjHom_isometry _ x
    refine ⟨horth, ?_⟩
    obtain ⟨l, hl, hσl, -⟩ := exists_symmetry_prod_eq_length_le Q hQ horth
    have hσl' : conjM0 u = symProd l hl := hσl
    change LinearEquiv.det (conjM0 u) = 1
    rw [hσl', det_symProd]
    by_contra hodd
    have hodd' : Odd l.length := by
      rw [← Nat.not_even_iff_odd]; intro he; exact hodd (by rw [he.neg_one_pow])
    -- `v = w⁻¹ u` anticommutes with `V` and is odd
    set w := vecProd l hl
    set u' : cliffordGroup Q := Subgroup.inclusion M0_le u
    have hneg : (LinearEquiv.neg k : V ≃ₗ[k] V) ^ l.length = LinearEquiv.neg k := by
      obtain ⟨m, hm⟩ := hodd'
      rw [hm, pow_succ, pow_mul, negE_sq, one_pow, one_mul]
    have hTw : conjHom w = LinearEquiv.neg k * conjHom u' := by
      rw [conjHom_vecProd, hneg, ← hσl']; rfl
    set v : cliffordGroup Q := w⁻¹ * u'
    have hTv : ∀ x, conjHom v x = -x := by
      intro x
      simp only [v, map_mul, map_inv, hTw, mul_inv_rev, LinearEquiv.mul_apply]
      rw [show (LinearEquiv.neg k : V ≃ₗ[k] V)⁻¹ = LinearEquiv.neg k by
        rw [inv_eq_iff_mul_eq_one, ← sq, negE_sq]]
      change (conjHom u')⁻¹ (-(conjHom u' x)) = -x
      rw [map_neg]
      change -((conjHom u').symm (conjHom u' x)) = -x
      rw [LinearEquiv.symm_apply_apply]
    have hanti : ∀ x, ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q x =
        -(ι Q x * ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
      intro x
      have h1 := conjHom_spec v x
      rw [hTv, map_neg] at h1
      have := congrArg (· * ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) h1
      simp only [mul_assoc, Units.inv_mul, mul_one, neg_mul] at this
      exact this.symm
    have hw1 : ((w : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 1 := by
      have := vecProd_mem_evenOdd l hl
      rwa [(ZMod.natCast_eq_one_iff_odd).2 hodd'] at this
    have hwi : (((w⁻¹ : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 1 :=
      mem_evenOdd_of_mul_eq_one Q hw1 (w : (CliffordAlgebra Q)ˣ).mul_inv
    have hv1 : ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 1 := by
      have := SetLike.mul_mem_graded hwi u.2.1
      simpa [v, u'] using this
    exact Units.ne_zero _ (eq_zero_of_odd_anticomm hQ hv1 hanti)
  · intro hσ
    obtain ⟨l, hl, hev, -, hT⟩ := exists_M0_of_orthPlus hQ hσ
    exact ⟨⟨(vecProd l hl : (CliffordAlgebra Q)ˣ), vecProd_mem_even hl hev, (vecProd l hl).2⟩, hT⟩

/-- **Cassels, Ch. 10, Theorem 3.1, p. 176 (kernel).** For $u \in M_0(V)$: $T_u = 1$ if and only if $u \in k$. -/
@[kb "cassels1978" "Ch. 10, Theorem 3.1, p. 176 (kernel)"]
theorem conjM0_eq_one_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (u : M0 Q) :
    conjM0 u = 1 ↔ ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      Set.range (algebraMap k (CliffordAlgebra Q)) :=
  conjHom_eq_one_iff hQ u.2.1

end SpinOrth

end QuadFormsKB.Cassels
