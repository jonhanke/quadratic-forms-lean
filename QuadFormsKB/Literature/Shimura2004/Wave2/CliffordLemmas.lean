/-
# Shimura 2004, §§2–3: the lemmas on special elements of the Clifford group

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I: Lemma 2.7 (printed
p. 19), Lemmas 3.10 and 3.11 (p. 25), (3.21) (p. 28). Page numbers are printed pages.

**Setting and dictionary.** As in `QuadFormsKB/Literature/Shimura2004/CliffordGroups.lean`: $F$ a field of
characteristic $\ne 2$, `Q : QuadraticForm F V` with $Q(x) = \varphi[x]$, $A(V)$ = `CliffordAlgebra Q`, the canonical
automorphism $a \mapsto a'$ = `involute`, the canonical involution $a \mapsto a^*$ = `reverse`, $G^+(V)$ =
`Cassels.M0 Q`, $G'(V)$ = `homogeneousCliffordGroup Q`, $\nu$ = `multiplier`, $\tau(a) : x \mapsto a^{-1}xa$ = `tau`.
Shimura's identity $xy + yx = 2\varphi(x,y)$ is Mathlib's `ι_mul_ι_add_swap` with $2\varphi(x,y)$ =
`QuadraticMap.polar Q x y`. A *weak Witt decomposition* $V = U + Fe + Ff$ (Shimura (2.6a,b)) has $e^2 = f^2 = 0$,
$ef + fe = 1$ and $U = (Fe + Ff)^\perp$; here: `Q e = 0`, `Q f = 0`, `polar Q e f = 1`, and $U$ is the set of $u$
with `polar Q u e = 0` and `polar Q u f = 0`.

**Proves** (all unconditional; standard axioms only)
* Lemma 3.10: $e(a,b) = a\,ef + b\,fe$ (3.11) gives a homomorphism $F^\times \times F^\times \to G^+(V)$
  (`eabHom`, `eabHom_mem_M0`), $e(a,b)^* = e(b,a) = (e+f)e(a,b)(e+f)$ (`reverse_eab`, `eab_conj_e_add_f`),
  $\nu(e(a,b)) = ab$ (`multiplier_eab`) and (3.12a) $(u + re + sf)\tau(e(a,b)) = u + (b/a)re + (a/b)sf$
  (`tau_eab`); and (3.12b) $(u + re + sf)\tau(qe + f) = -u + qse + q^{-1}rf$ (`tau_qe_add_f`).
* Lemma 3.11: for $g = r + xy$, $gg^* \in F$ (`mul_reverse_rxy`), $gVg^* \subseteq V$ (`rxy_conj_mem`), and
  $g \in G^+(V)$ when $gg^* \ne 0$ (`rxy_mem_M0`).
* (3.21): the homomorphism $\mu : G'(V) \to F^\times$, $\mu = \nu$ on $G^+(V)$ and $-\nu$ on $G^-(V)$
  (`muHom`, `muHom_of_mem_M0`, `muHom_of_mem_odd`), characterized by $\mu(a) = a'a^*$ (`algebraMap_muHom`).
* Lemma 2.7 (i), (ii): for an orthogonal family $h_1, \dots, h_n$ and $z = h_1\cdots h_n$:
  $xz = (-1)^{n-1}zx$ for every $x$ in the span of the $h_i$, hence for every $x \in V$ when they form a basis
  (`vec_mul_orthProd`; for invertible $z$ this is $z^{-1}xz = (-1)^{n-1}x$), $z^2 = (-1)^{n(n-1)/2}h_1^2\cdots h_n^2$
  (`orthProd_sq`) and $z^* = (-1)^{n(n-1)/2}z$ (`reverse_orthProd`); and the part of (iv) that follows from (i):
  for $n$ odd $z$ is in the center of $A(V)$ (`orthProd_mem_center_of_odd`).
-/
import QuadFormsKB.Literature.Shimura2004.CliffordParity
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

theorem algebraMap_injective_clifford : Function.Injective (algebraMap F A) :=
  (algebraMap F A).injective

theorem isOrtho_of_polar_eq_zero {x y : V} (h : QuadraticMap.polar Q x y = 0) : Q.IsOrtho x y := by
  rw [QuadraticMap.isOrtho_def]
  rw [QuadraticMap.polar, sub_sub, sub_eq_zero] at h
  exact h

/-! ### Lemma 3.10: the elements $e(a,b) = a\,ef + b\,fe$ -/

section WeakWitt

variable {e f : V}

/-- In a weak Witt decomposition, $ef$ and $fe$ are orthogonal idempotents with sum $1$. -/
theorem ef_add_fe (hef : QuadraticMap.polar Q e f = 1) : ι Q e * ι Q f + ι Q f * ι Q e = 1 := by
  rw [ι_mul_ι_add_swap, hef, map_one]

theorem ι_sq_zero {x : V} (hx : Q x = 0) : ι Q x * ι Q x = 0 := by
  rw [ι_sq_scalar, hx, map_zero]

theorem efe (he : Q e = 0) (hef : QuadraticMap.polar Q e f = 1) : ι Q e * ι Q f * ι Q e = ι Q e := by
  have h := ef_add_fe hef
  calc ι Q e * ι Q f * ι Q e = ι Q e * (ι Q f * ι Q e) := mul_assoc _ _ _
    _ = ι Q e * (1 - ι Q e * ι Q f) := by rw [← h]; abel_nf
    _ = ι Q e := by rw [mul_sub, mul_one, ← mul_assoc, ι_sq_zero he, zero_mul, sub_zero]

theorem fef (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) : ι Q f * ι Q e * ι Q f = ι Q f := by
  have h := ef_add_fe hef
  calc ι Q f * ι Q e * ι Q f = ι Q f * (ι Q e * ι Q f) := mul_assoc _ _ _
    _ = ι Q f * (1 - ι Q f * ι Q e) := by rw [← h]; abel_nf
    _ = ι Q f := by rw [mul_sub, mul_one, ← mul_assoc, ι_sq_zero hf, zero_mul, sub_zero]

variable (Q e f) in
/-- **The element** $e(a,b) = a\,ef + b\,fe$ (Shimura (3.11), p. 25), for $a, b \in F$. -/
@[kb "shimura2004" "(3.11), p. 25 (e(a, b) = a·ef + b·fe)"]
def eab (a b : F) : A := a • (ι Q e * ι Q f) + b • (ι Q f * ι Q e)

theorem eab_mul (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (a b c d : F) :
    eab Q e f a b * eab Q e f c d = eab Q e f (a * c) (b * d) := by
  have h1 : ι Q e * ι Q f * (ι Q e * ι Q f) = ι Q e * ι Q f := by rw [← mul_assoc, efe he hef]
  have h2 : ι Q f * ι Q e * (ι Q f * ι Q e) = ι Q f * ι Q e := by rw [← mul_assoc, fef hf hef]
  have h3 : ι Q e * ι Q f * (ι Q f * ι Q e) = 0 := by
    rw [mul_assoc, ← mul_assoc (ι Q f), ι_sq_zero hf, zero_mul, mul_zero]
  have h4 : ι Q f * ι Q e * (ι Q e * ι Q f) = 0 := by
    rw [mul_assoc, ← mul_assoc (ι Q e), ι_sq_zero he, zero_mul, mul_zero]
  simp only [eab, add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, h4, smul_zero, add_zero, zero_add]

theorem eab_one_one (hef : QuadraticMap.polar Q e f = 1) : eab Q e f 1 1 = 1 := by
  simp [eab, ef_add_fe hef]

/-- $e(a,b)^* = e(b,a)$ (Lemma 3.10). -/
@[kb "shimura2004" "Lemma 3.10, p. 25 (e(a, b)* = e(b, a))"]
theorem reverse_eab (a b : F) : reverse (eab Q e f a b) = eab Q e f b a := by
  simp only [eab, map_add, map_smul, reverse.map_mul, reverse_ι]
  exact add_comm _ _

/-- $(e+f)\,e(b,a)\,(e+f) = e(a,b)$ (Lemma 3.10). -/
@[kb "shimura2004" "Lemma 3.10, p. 25 (e(b, a) = (e + f)e(a, b)(e + f))"]
theorem eab_conj_e_add_f (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (a b : F) :
    ι Q (e + f) * eab Q e f b a * ι Q (e + f) = eab Q e f a b := by
  have ee : ∀ x : A, ι Q e * (ι Q e * x) = 0 := fun x => by rw [← mul_assoc, ι_sq_zero he, zero_mul]
  have ff : ∀ x : A, ι Q f * (ι Q f * x) = 0 := fun x => by rw [← mul_assoc, ι_sq_zero hf, zero_mul]
  have k1 : ι Q (e + f) * (ι Q e * ι Q f) * ι Q (e + f) = ι Q f * ι Q e := by
    simp only [map_add, add_mul, mul_add, mul_assoc, ee, ff, ι_sq_zero he, ι_sq_zero hf, mul_zero, zero_add,
      add_zero]
    rw [← mul_assoc (ι Q e) (ι Q f), ← mul_assoc, ← mul_assoc, fef hf hef]
  have k2 : ι Q (e + f) * (ι Q f * ι Q e) * ι Q (e + f) = ι Q e * ι Q f := by
    simp only [map_add, add_mul, mul_add, mul_assoc, ee, ff, ι_sq_zero he, ι_sq_zero hf, mul_zero, zero_add,
      add_zero]
    rw [← mul_assoc (ι Q f) (ι Q e), ← mul_assoc, ← mul_assoc, efe he hef]
  simp only [eab, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, k1, k2]
  exact add_comm _ _

theorem eab_mem_evenOdd_zero (a b : F) : eab Q e f a b ∈ evenOdd Q 0 :=
  add_mem (Submodule.smul_mem _ _ (ι_mul_ι_mem_evenOdd_zero Q e f))
    (Submodule.smul_mem _ _ (ι_mul_ι_mem_evenOdd_zero Q f e))

/-- Conjugation formulas behind (3.12a): $e(a,b)\,e\,e(c,d) = ad\,e$. -/
theorem eab_e_eab (he : Q e = 0) (hef : QuadraticMap.polar Q e f = 1) (a b c d : F) :
    eab Q e f a b * ι Q e * eab Q e f c d = (a * d) • ι Q e := by
  have k1 : (ι Q e * ι Q f) * ι Q e = ι Q e := efe he hef
  have k2 : (ι Q f * ι Q e) * ι Q e = 0 := by rw [mul_assoc, ι_sq_zero he, mul_zero]
  have k3 : ι Q e * (ι Q e * ι Q f) = 0 := by rw [← mul_assoc, ι_sq_zero he, zero_mul]
  have k4 : ι Q e * (ι Q f * ι Q e) = ι Q e := by rw [← mul_assoc, efe he hef]
  simp only [eab, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, k1, k2, k3, k4, smul_zero, add_zero,
    zero_add, smul_smul]
  rw [mul_comm]

/-- $e(a,b)\,f\,e(c,d) = bc\,f$. -/
theorem eab_f_eab (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (a b c d : F) :
    eab Q e f a b * ι Q f * eab Q e f c d = (b * c) • ι Q f := by
  have k1 : (ι Q e * ι Q f) * ι Q f = 0 := by rw [mul_assoc, ι_sq_zero hf, mul_zero]
  have k2 : (ι Q f * ι Q e) * ι Q f = ι Q f := fef hf hef
  have k3 : ι Q f * (ι Q e * ι Q f) = ι Q f := by rw [← mul_assoc, fef hf hef]
  have k4 : ι Q f * (ι Q f * ι Q e) = 0 := by rw [← mul_assoc, ι_sq_zero hf, zero_mul]
  simp only [eab, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, k1, k2, k3, k4, smul_zero, add_zero,
    zero_add, smul_smul]
  rw [mul_comm]

/-- A vector $u \perp e, f$ commutes with $ef$ and $fe$, hence with $e(a,b)$. -/
theorem eab_commute_of_perp {u : V} (hue : QuadraticMap.polar Q u e = 0) (huf : QuadraticMap.polar Q u f = 0)
    (a b : F) : ι Q u * eab Q e f a b = eab Q e f a b * ι Q u := by
  have oe : Q.IsOrtho u e := isOrtho_of_polar_eq_zero hue
  have of : Q.IsOrtho u f := isOrtho_of_polar_eq_zero huf
  have c1 : ι Q u * (ι Q e * ι Q f) = ι Q e * ι Q f * ι Q u := by
    rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho oe, neg_mul, mul_assoc, ι_mul_ι_comm_of_isOrtho of, mul_neg,
      neg_neg, mul_assoc]
  have c2 : ι Q u * (ι Q f * ι Q e) = ι Q f * ι Q e * ι Q u := by
    rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho of, neg_mul, mul_assoc, ι_mul_ι_comm_of_isOrtho oe, mul_neg,
      neg_neg, mul_assoc]
  simp only [eab, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, c1, c2]

/-- Every $x \in V$ is $u + re + sf$ with $u \perp e, f$: $r = 2\varphi(x,f)$, $s = 2\varphi(x,e)$. -/
theorem decomp_weakWitt (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (x : V) :
    let u := x - QuadraticMap.polar Q x f • e - QuadraticMap.polar Q x e • f
    QuadraticMap.polar Q u e = 0 ∧ QuadraticMap.polar Q u f = 0 := by
  have hee : QuadraticMap.polar Q e e = 0 := by rw [QuadraticMap.polar_self, he, smul_zero]
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hfe : QuadraticMap.polar Q f e = 1 := by rw [QuadraticMap.polar_comm, hef]
  refine ⟨?_, ?_⟩ <;>
  simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hee, hff, hef, hfe, smul_eq_mul,
    mul_zero, mul_one, sub_zero, sub_self]

theorem eab_self (hef : QuadraticMap.polar Q e f = 1) (k : F) : eab Q e f k k = algebraMap F A k := by
  rw [eab, ← smul_add, ef_add_fe hef, Algebra.algebraMap_eq_smul_one]

/-- $e(a,b)\,x\,e(c,d) \in V$ for every $x \in V$ when $ac = bd$, explicitly: with $x = u + re + sf$,
$u \perp e, f$, it is $ac\,u + ad\,re + bc\,sf$. -/
theorem eab_vec_eab (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) {a b c d : F}
    (hk : a * c = b * d) (x : V) :
    eab Q e f a b * ι Q x * eab Q e f c d =
      ι Q ((a * c) • (x - QuadraticMap.polar Q x f • e - QuadraticMap.polar Q x e • f) +
        (a * d * QuadraticMap.polar Q x f) • e + (b * c * QuadraticMap.polar Q x e) • f) := by
  obtain ⟨hue, huf⟩ := decomp_weakWitt he hf hef x
  set r := QuadraticMap.polar Q x f
  set s := QuadraticMap.polar Q x e
  set u := x - r • e - s • f with hu
  have hx : x = u + r • e + s • f := by rw [hu]; abel
  have hU : eab Q e f a b * ι Q u * eab Q e f c d = (a * c) • ι Q u := by
    calc eab Q e f a b * ι Q u * eab Q e f c d = ι Q u * (eab Q e f a b * eab Q e f c d) := by
          rw [← eab_commute_of_perp hue huf, mul_assoc]
      _ = ι Q u * algebraMap F A (a * c) := by rw [eab_mul he hf hef, ← hk, eab_self hef]
      _ = (a * c) • ι Q u := by rw [← Algebra.commutes, ← Algebra.smul_def]
  conv_lhs => rw [hx]
  rw [map_add, map_add, map_smul, map_smul, mul_add, mul_add, add_mul, add_mul, hU, mul_smul_comm,
    mul_smul_comm, smul_mul_assoc, smul_mul_assoc, eab_e_eab he hef, eab_f_eab hf hef, smul_smul, smul_smul,
    map_add, map_add, map_smul, map_smul, map_smul]
  ring_nf

/-- $e(a,b)$ is invertible for $a, b \ne 0$, with inverse $e(a^{-1}, b^{-1})$. -/
def eabUnit (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (a b : Fˣ) : Aˣ where
  val := eab Q e f a b
  inv := eab Q e f (a⁻¹ : Fˣ) (b⁻¹ : Fˣ)
  val_inv := by rw [eab_mul he hf hef]; simp [eab_one_one hef]
  inv_val := by rw [eab_mul he hf hef]; simp [eab_one_one hef]

/-- **Lemma 3.10** (Shimura 2004, p. 25), first assertion: $(a,b) \mapsto e(a,b)$ is a homomorphism of
$F^\times \times F^\times$ into $A(V)^\times$, with values in $G^+(V)$ (`eabHom_mem_M0`). -/
@[kb "shimura2004" "Lemma 3.10, p. 25 ((a, b) ↦ e(a, b) is a homomorphism F^× × F^× → G⁺(V))"]
def eabHom (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) : Fˣ × Fˣ →* Aˣ where
  toFun p := eabUnit he hf hef p.1 p.2
  map_one' := Units.ext (by simp [eabUnit, eab_one_one hef])
  map_mul' p q := Units.ext (by simp [eabUnit, eab_mul he hf hef])

theorem coe_eabHom (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (a b : Fˣ) :
    ((eabHom he hf hef (a, b) : Aˣ) : A) = eab Q e f a b := rfl

/-- **Lemma 3.10**: $e(a,b) \in G^+(V)$ (by (3.5): $e(a,b)e(a,b)^* = ab$ and $e(a,b)Ve(a,b)^* \subseteq V$). -/
@[kb "shimura2004" "Lemma 3.10, p. 25 (e(a, b) ∈ G⁺(V))"]
theorem eabHom_mem_M0 (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (p : Fˣ × Fˣ) :
    eabHom he hf hef p ∈ M0 Q := by
  obtain ⟨u, hu, hM⟩ := mem_M0_of_mul_reverse (Q := Q) (eab_mem_evenOdd_zero (Q := Q) (e := e) (f := f) p.1 p.2)
    (mul_ne_zero p.1.ne_zero p.2.ne_zero)
    (by rw [reverse_eab, eab_mul he hf hef, mul_comm (p.2 : F), eab_self hef])
    (fun x => ⟨_, by rw [reverse_eab, eab_vec_eab he hf hef (mul_comm _ _)]⟩)
  have : u = eabHom he hf hef p := Units.ext hu
  exact this ▸ hM

/-- **Lemma 3.10**: $\nu(e(a,b)) = ab$. -/
@[kb "shimura2004" "Lemma 3.10, p. 25 (ν(e(a, b)) = ab)"]
theorem multiplier_eab (hQ : (QuadraticMap.associated Q).Nondegenerate) (he : Q e = 0) (hf : Q f = 0)
    (hef : QuadraticMap.polar Q e f = 1) (a b : Fˣ) :
    (multiplier hQ ⟨eabHom he hf hef (a, b), M0_le_homogeneous (eabHom_mem_M0 he hf hef (a, b))⟩ : F) =
      a * b := by
  apply algebraMap_injective_clifford (Q := Q)
  rw [algebraMap_multiplier]
  change eab Q e f a b * reverse (eab Q e f a b) = _
  rw [reverse_eab, eab_mul he hf hef, mul_comm (b : F), eab_self hef]

/-- **(3.12a)** (Shimura 2004, p. 25): $(u + re + sf)\tau(e(a,b)) = u + (b/a)re + (a/b)sf$ for $u \perp e, f$;
here with $r = 2\varphi(x, f)$, $s = 2\varphi(x, e)$ and $u = x - re - sf$, so $\tau(e(a,b))$ is
$\mathrm{diag}[a/b, 1_U, b/a]$ on $Ff + U + Fe$. -/
@[kb "shimura2004" "(3.12a), p. 25 ((u + re + sf)τ(e(a, b)) = u + (b/a)re + (a/b)sf)"]
theorem tau_eab (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (a b : Fˣ) (x : V) :
    tau ⟨eabHom he hf hef (a, b), M0_le (eabHom_mem_M0 he hf hef (a, b))⟩ x =
      (x - QuadraticMap.polar Q x f • e - QuadraticMap.polar Q x e • f) +
        ((b / a : F) * QuadraticMap.polar Q x f) • e + ((a / b : F) * QuadraticMap.polar Q x e) • f := by
  apply cliffordι_injective Q
  rw [tau_spec]
  change eab Q e f (a⁻¹ : Fˣ) (b⁻¹ : Fˣ) * ι Q x * eab Q e f a b = _
  rw [eab_vec_eab he hf hef (by simp [mul_comm])]
  congr 1
  simp only [Units.val_inv_eq_inv_val, ne_eq, Units.ne_zero, not_false_eq_true, inv_mul_cancel₀, one_smul]
  rw [div_eq_inv_mul, div_eq_inv_mul, mul_comm (a : F)⁻¹ (b : F), mul_comm (b : F)⁻¹ (a : F)]

/-- An invertible vector, as an element of $G(V)$. -/
def vecCG (v : V) (hv : Q v ≠ 0) : cliffordGroup Q :=
  ⟨vecUnit v hv, homogeneous_le_cliffordGroup (cliffordGroupOdd_subset_homogeneous (vecUnit_mem_cliffordGroupOdd v hv))⟩

/-- $x\tau(v) = v^{-1}xv = \varphi[v]^{-1}(2\varphi(v,x)v - \varphi[v]x)$ for an invertible vector $v$. -/
theorem tau_vecCG (v : V) (hv : Q v ≠ 0) (x : V) :
    tau (vecCG v hv) x = (Q v)⁻¹ • (QuadraticMap.polar Q v x • v - Q v • x) := by
  apply cliffordι_injective Q
  rw [tau_spec, map_smul, ← ι_mul_ι_mul_ι]
  change ((Q v)⁻¹ • ι Q v) * ι Q x * ι Q v = _
  rw [smul_mul_assoc, smul_mul_assoc]

theorem Q_qe_add_f (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) (q : F) :
    Q (q • e + f) = q := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, he, hf, QuadraticMap.polar_smul_left, hef]; simp

/-- **(3.12b)** (Shimura 2004, p. 25): for $q \in F^\times$, $(u + re + sf)\tau(qe + f) = -u + qse + q^{-1}rf$ for
$u \perp e, f$; here with $r = 2\varphi(x, f)$, $s = 2\varphi(x, e)$, $u = x - re - sf$. -/
@[kb "shimura2004" "(3.12b), p. 25 ((u + re + sf)τ(qe + f) = −u + qse + q⁻¹rf)"]
theorem tau_qe_add_f (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1) {q : F} (hq : q ≠ 0)
    (x : V) :
    tau (vecCG (q • e + f) (by rwa [Q_qe_add_f he hf hef])) x =
      -(x - QuadraticMap.polar Q x f • e - QuadraticMap.polar Q x e • f) +
        (q * QuadraticMap.polar Q x e) • e + (q⁻¹ * QuadraticMap.polar Q x f) • f := by
  rw [tau_vecCG, Q_qe_add_f he hf hef]
  have hp : QuadraticMap.polar Q (q • e + f) x = q * QuadraticMap.polar Q x e + QuadraticMap.polar Q x f := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_comm Q e x,
      QuadraticMap.polar_comm Q f x, smul_eq_mul]
  rw [hp]
  set s := QuadraticMap.polar Q x e
  set r := QuadraticMap.polar Q x f
  have h1 : q⁻¹ * (q * s + r) * q = q * s + r := by field_simp
  have h2 : q⁻¹ * (q * s + r) = s + q⁻¹ * r := by field_simp
  have h3 : q⁻¹ * q = 1 := inv_mul_cancel₀ hq
  simp only [smul_sub, smul_add, smul_smul, h1, h2, h3, one_smul]
  match_scalars <;> field_simp <;> ring

end WeakWitt

/-! ### Lemma 3.11: the elements $g = r + xy$ -/

section Rxy

variable (Q) in
/-- The element $g = r + xy$ of Lemma 3.11 ($r \in F$, $x, y \in V$). -/
def rxy (r : F) (x y : V) : A := algebraMap F A r + ι Q x * ι Q y

theorem reverse_rxy (r : F) (x y : V) : reverse (rxy Q r x y) = algebraMap F A r + ι Q y * ι Q x := by
  simp [rxy, reverse.map_mul]

/-- **Lemma 3.11** (Shimura 2004, p. 25), first assertion: $gg^* \in F$ for $g = r + xy$; explicitly
$gg^* = r^2 + r(xy + yx) + x^2y^2 = r^2 + 2r\varphi(x,y) + \varphi[x]\varphi[y]$. -/
@[kb "shimura2004" "Lemma 3.11, p. 25 (gg* ∈ F for g = r + xy)"]
theorem mul_reverse_rxy (r : F) (x y : V) :
    rxy Q r x y * reverse (rxy Q r x y) =
      algebraMap F A (r ^ 2 + r * QuadraticMap.polar Q x y + Q x * Q y) := by
  rw [reverse_rxy, rxy]
  have hXX : ι Q x * (ι Q y * (ι Q y * ι Q x)) = (Q x * Q y) • (1 : A) := by
    rw [← mul_assoc (ι Q y) (ι Q y), ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
  have h3 : QuadraticMap.polar Q x y • (1 : A) = ι Q x * ι Q y + ι Q y * ι Q x := by
    rw [ι_mul_ι_add_swap, Algebra.algebraMap_eq_smul_one]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul, add_smul, mul_smul r, h3, ← hXX]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul, mul_assoc,
    pow_two]
  abel

/-- $xyw + wyx \in V$: it is $2\varphi(y,w)x - 2\varphi(x,w)y + 2\varphi(x,y)w$. -/
theorem xyw_add_wyx (x y w : V) :
    ι Q x * ι Q y * ι Q w + ι Q w * ι Q y * ι Q x =
      ι Q (QuadraticMap.polar Q y w • x - QuadraticMap.polar Q x w • y + QuadraticMap.polar Q x y • w) := by
  have h1 : ι Q y * ι Q w = QuadraticMap.polar Q y w • (1 : A) - ι Q w * ι Q y := by
    rw [ι_mul_ι_comm, Algebra.algebraMap_eq_smul_one]
  have h2 : ι Q x * ι Q w = QuadraticMap.polar Q x w • (1 : A) - ι Q w * ι Q x := by
    rw [ι_mul_ι_comm, Algebra.algebraMap_eq_smul_one]
  have h3 : ι Q x * ι Q y = QuadraticMap.polar Q x y • (1 : A) - ι Q y * ι Q x := by
    rw [ι_mul_ι_comm, Algebra.algebraMap_eq_smul_one]
  rw [map_add, map_sub, map_smul, map_smul, map_smul, mul_assoc (ι Q x), h1, mul_sub, mul_smul_comm, mul_one,
    ← mul_assoc (ι Q x) (ι Q w), h2, sub_mul, smul_mul_assoc, one_mul, mul_assoc (ι Q w) (ι Q x), h3, mul_sub,
    mul_smul_comm, mul_one]
  simp only [mul_assoc]
  abel

/-- **Lemma 3.11** (Shimura 2004, p. 25), second assertion: $gVg^* \subseteq V$ for $g = r + xy$. -/
@[kb "shimura2004" "Lemma 3.11, p. 25 (gVg* ⊆ V for g = r + xy)"]
theorem rxy_conj_mem (r : F) (x y w : V) : ∃ z : V, ι Q z = rxy Q r x y * ι Q w * reverse (rxy Q r x y) := by
  refine ⟨r ^ 2 • w + r • (QuadraticMap.polar Q y w • x - QuadraticMap.polar Q x w • y +
      QuadraticMap.polar Q x y • w) +
    (QuadraticMap.polar Q x (QuadraticMap.polar Q y w • y - Q y • w) • x -
      Q x • (QuadraticMap.polar Q y w • y - Q y • w)), ?_⟩
  have hyy : ι Q y * ι Q w * ι Q y = ι Q (QuadraticMap.polar Q y w • y - Q y • w) := ι_mul_ι_mul_ι y w
  have hxx := ι_mul_ι_mul_ι (Q := Q) x (QuadraticMap.polar Q y w • y - Q y • w)
  have hsum := xyw_add_wyx (Q := Q) x y w
  rw [reverse_rxy, rxy, map_add, map_add, map_smul, map_smul, ← hxx, ← hsum, ← hyy,
    Algebra.algebraMap_eq_smul_one]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul, mul_assoc,
    pow_two]
  abel

/-- **Lemma 3.11** (Shimura 2004, p. 25), third assertion: $g = r + xy \in G^+(V)$ if $gg^* \ne 0$. -/
@[kb "shimura2004" "Lemma 3.11, p. 25 (g = r + xy ∈ G⁺(V) if gg* ≠ 0)"]
theorem rxy_mem_M0 (r : F) (x y : V) (h : r ^ 2 + r * QuadraticMap.polar Q x y + Q x * Q y ≠ 0) :
    ∃ u : (CliffordAlgebra Q)ˣ, (u : A) = rxy Q r x y ∧ u ∈ M0 Q :=
  mem_M0_of_mul_reverse (add_mem (algebraMap_mem_evenOdd_zero r) (ι_mul_ι_mem_evenOdd_zero Q x y)) h
    (mul_reverse_rxy r x y) (rxy_conj_mem r x y)

end Rxy

/-! ### (3.21): the homomorphism $\mu$ -/

section Mu

variable (hQ : (QuadraticMap.associated Q).Nondegenerate)

open Classical in
/-- The values of $\mu$ (3.21): $\nu(a)$ on $G^+(V)$ and $-\nu(a)$ on $G^-(V)$. -/
def muFun (a : homogeneousCliffordGroup Q) : Fˣ :=
  if ((a : (CliffordAlgebra Q)ˣ) : A) ∈ evenOdd Q 0 then multiplier hQ a else -multiplier hQ a

/-- $\mu(a) = a'a^*$ ($a'$ the canonical automorphism): the sign of $a' = \pm a$ is the sign in (3.21). -/
theorem algebraMap_muFun (a : homogeneousCliffordGroup Q) :
    algebraMap F A (muFun hQ a : F) =
      involute ((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A) := by
  unfold muFun
  split_ifs with h
  · rw [involute_eq_of_mem_even h, algebraMap_multiplier]
  · rcases a.2.2 with h' | h'
    · exact absurd h' h
    · rw [involute_eq_of_mem_odd h', Units.val_neg, map_neg, algebraMap_multiplier, neg_mul]

/-- **The homomorphism** $\mu : G'(V) \to F^\times$ of (3.21) (Shimura 2004, p. 28): $\mu(a) = \nu(a)$ for
$a \in G^+(V)$ and $\mu(a) = -\nu(a)$ for $a \in G^-(V)$; nondegenerate $\varphi$. -/
@[kb "shimura2004" "(3.21), p. 28 (μ : G'(V) → F^×, ν on G⁺(V), −ν on G⁻(V))"]
def muHom : homogeneousCliffordGroup Q →* Fˣ where
  toFun := muFun hQ
  map_one' := by
    ext
    apply algebraMap_injective_clifford (Q := Q)
    rw [algebraMap_muFun]
    simp
  map_mul' a b := by
    ext
    apply algebraMap_injective_clifford (Q := Q)
    change algebraMap F A (muFun hQ (a * b) : F) = algebraMap F A ((muFun hQ a : F) * (muFun hQ b : F))
    rw [algebraMap_muFun hQ (a * b)]
    calc involute (((a * b : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) : A) *
          reverse (((a * b : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) : A)
        = involute ((a : (CliffordAlgebra Q)ˣ) : A) *
            (involute ((b : (CliffordAlgebra Q)ˣ) : A) * reverse ((b : (CliffordAlgebra Q)ˣ) : A)) *
            reverse ((a : (CliffordAlgebra Q)ˣ) : A) := by
          simp only [Subgroup.coe_mul, Units.val_mul, map_mul, reverse.map_mul, mul_assoc]
      _ = algebraMap F A (muFun hQ b : F) *
            (involute ((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A)) := by
          rw [← algebraMap_muFun hQ b, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [← algebraMap_muFun hQ a, ← map_mul, mul_comm]

theorem algebraMap_muHom (a : homogeneousCliffordGroup Q) :
    algebraMap F A (muHom hQ a : F) =
      involute ((a : (CliffordAlgebra Q)ˣ) : A) * reverse ((a : (CliffordAlgebra Q)ˣ) : A) :=
  algebraMap_muFun hQ a

theorem muHom_of_mem_M0 (a : homogeneousCliffordGroup Q) (h : (a : (CliffordAlgebra Q)ˣ) ∈ M0 Q) :
    muHom hQ a = multiplier hQ a := by
  simp [muHom, muFun, h.1]

theorem muHom_of_mem_odd (a : homogeneousCliffordGroup Q)
    (h : (a : (CliffordAlgebra Q)ˣ) ∈ cliffordGroupOdd Q) : muHom hQ a = -multiplier hQ a := by
  have hdisj := (evenOdd_isCompl Q).disjoint
  rw [Submodule.disjoint_def] at hdisj
  have hn : ((a : (CliffordAlgebra Q)ˣ) : A) ∉ evenOdd Q 0 := fun h0 =>
    (a : (CliffordAlgebra Q)ˣ).ne_zero (hdisj _ h0 h.2)
  simp [muHom, muFun, hn]

end Mu

/-! ### Lemma 2.7: the product $z = h_1\cdots h_n$ of an orthogonal family -/

section OrthProd

variable (Q) in
/-- $z = h_1\cdots h_n$, the product in $A(V)$ of the vectors of a list. -/
def orthProd (l : List V) : A := (l.map (ι Q)).prod

theorem orthProd_cons (a : V) (l : List V) : orthProd Q (a :: l) = ι Q a * orthProd Q l := by
  simp [orthProd]

/-- A vector orthogonal to $h_1, \dots, h_m$ anticommutes with each, so $vz = (-1)^m zv$. -/
theorem vec_mul_orthProd_of_perp (v : V) (l : List V) (h : ∀ y ∈ l, QuadraticMap.polar Q v y = 0) :
    ι Q v * orthProd Q l = (-1 : F) ^ l.length • (orthProd Q l * ι Q v) := by
  induction l with
  | nil => simp [orthProd]
  | cons a t ih =>
    rw [orthProd_cons, ← mul_assoc, ι_mul_ι_comm_of_isOrtho (isOrtho_of_polar_eq_zero (h a (by simp))),
      neg_mul, mul_assoc, ih (fun y hy => h y (by simp [hy])), mul_smul_comm, List.length_cons, pow_succ,
      mul_assoc]
    simp [mul_assoc, neg_smul]

/-- For a pairwise orthogonal list $h_1, \dots, h_n$ and each $h_i$: $h_iz = (-1)^{n-1}zh_i$. -/
theorem mem_mul_orthProd (l : List V) (hl : l.Pairwise (fun a b => QuadraticMap.polar Q a b = 0)) :
    ∀ x ∈ l, ι Q x * orthProd Q l = (-1 : F) ^ (l.length - 1) • (orthProd Q l * ι Q x) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hl
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [orthProd_cons, mul_assoc, vec_mul_orthProd_of_perp x t hl.1]
      simp [mul_smul_comm, mul_assoc]
    · have hxa : QuadraticMap.polar Q x a = 0 := by rw [QuadraticMap.polar_comm]; exact hl.1 x hx
      obtain ⟨k, hk⟩ : ∃ k, t.length = k + 1 := Nat.exists_eq_succ_of_ne_zero (List.length_pos_of_mem hx).ne'
      rw [orthProd_cons, ← mul_assoc, ι_mul_ι_comm_of_isOrtho (isOrtho_of_polar_eq_zero hxa), neg_mul,
        mul_assoc, ih hl.2 x hx, List.length_cons, hk]
      simp [pow_succ, mul_smul_comm, mul_assoc, neg_smul]

/-- The relation $xz = (-1)^{n-1}zx$ extends linearly to the span of the $h_i$. -/
theorem vec_mul_orthProd_of_mem_span (l : List V) (hl : l.Pairwise (fun a b => QuadraticMap.polar Q a b = 0))
    {x : V} (hx : x ∈ Submodule.span F {y | y ∈ l}) :
    ι Q x * orthProd Q l = (-1 : F) ^ (l.length - 1) • (orthProd Q l * ι Q x) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact mem_mul_orthProd l hl y hy
  | zero => simp
  | add y w _ _ hy hw => rw [map_add, add_mul, mul_add, hy, hw, smul_add]
  | smul c y _ hy => rw [map_smul, smul_mul_assoc, hy, mul_smul_comm, smul_comm]

/-- $zh = (-1)^m hz$ rewritten the other way: $zv = (-1)^m vz$ for $v$ orthogonal to the list. -/
theorem orthProd_mul_vec_of_perp (v : V) (l : List V) (h : ∀ y ∈ l, QuadraticMap.polar Q v y = 0) :
    orthProd Q l * ι Q v = (-1 : F) ^ l.length • (ι Q v * orthProd Q l) := by
  rw [vec_mul_orthProd_of_perp v l h, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

theorem orthProd_sq_list (l : List V) (hl : l.Pairwise (fun a b => QuadraticMap.polar Q a b = 0)) :
    orthProd Q l * orthProd Q l = algebraMap F A ((-1 : F) ^ (l.length.choose 2) * (l.map Q).prod) := by
  induction l with
  | nil => simp [orthProd]
  | cons a t ih =>
    rw [List.pairwise_cons] at hl
    rw [orthProd_cons]
    calc ι Q a * orthProd Q t * (ι Q a * orthProd Q t) = ι Q a * (orthProd Q t * ι Q a) * orthProd Q t := by
          simp only [mul_assoc]
      _ = (-1 : F) ^ t.length • (ι Q a * ι Q a * (orthProd Q t * orthProd Q t)) := by
          rw [orthProd_mul_vec_of_perp a t hl.1, mul_smul_comm, smul_mul_assoc]; simp only [mul_assoc]
      _ = _ := by
          rw [ι_sq_scalar, ih hl.2, ← map_mul, Algebra.smul_def, ← map_mul]
          congr 1
          simp only [List.length_cons, List.map_cons, List.prod_cons, Nat.choose_succ_succ', Nat.choose_one_right,
            pow_add]
          ring

theorem reverse_orthProd_list (l : List V) (hl : l.Pairwise (fun a b => QuadraticMap.polar Q a b = 0)) :
    reverse (orthProd Q l) = (-1 : F) ^ (l.length.choose 2) • orthProd Q l := by
  induction l with
  | nil => simp [orthProd]
  | cons a t ih =>
    rw [List.pairwise_cons] at hl
    rw [orthProd_cons, reverse.map_mul, reverse_ι, ih hl.2, smul_mul_assoc, orthProd_mul_vec_of_perp a t hl.1,
      smul_smul, List.length_cons, Nat.choose_succ_succ', Nat.choose_one_right, pow_add]
    congr 1
    ring

/-! #### Lemma 2.7 for an orthogonal family $h_0, \dots, h_{n-1}$ -/

variable {n : ℕ} (h : Fin n → V)

theorem pairwise_ofFn_of_orth (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    (List.ofFn h).Pairwise (fun a b => QuadraticMap.polar Q a b = 0) :=
  List.pairwise_ofFn.2 fun i j hij => horth i j hij.ne

/-- **Lemma 2.7 (i)** (Shimura 2004, p. 19): for an orthogonal basis $h_0, \dots, h_{n-1}$ of $V$ (Shimura's
$h_1, \dots, h_n$) and $z = h_0 \cdots h_{n-1}$: $xz = (-1)^{n-1}zx$ for every $x \in V$, i.e.
$z^{-1}xz = (-1)^{n-1}x$ ($z$ is invertible when the $\varphi[h_i] \ne 0$, by (ii)). -/
@[kb "shimura2004" "Lemma 2.7 (i), p. 19 (z⁻¹xz = (−1)^{n−1}x for z = h₁⋯hₙ)"]
theorem vec_mul_orthProd (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (x : V) :
    ι Q x * orthProd Q (List.ofFn h) = (-1 : F) ^ (n - 1) • (orthProd Q (List.ofFn h) * ι Q x) := by
  have hx : x ∈ Submodule.span F {y | y ∈ List.ofFn h} := by
    have : {y | y ∈ List.ofFn h} = Set.range h := by ext y; simp [List.mem_ofFn]
    rw [this, hspan]; trivial
  simpa using vec_mul_orthProd_of_mem_span (List.ofFn h) (pairwise_ofFn_of_orth h horth) hx

/-- **Lemma 2.7 (ii)**, first formula (Shimura 2004, p. 19): $z^2 = (-1)^{n(n-1)/2}h_1^2\cdots h_n^2$ for an
orthogonal family $h_0, \dots, h_{n-1}$ and $z = h_0\cdots h_{n-1}$. -/
@[kb "shimura2004" "Lemma 2.7 (ii), p. 19 (z² = (−1)^{n(n−1)/2} h₁² ⋯ hₙ²)"]
theorem orthProd_sq (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    orthProd Q (List.ofFn h) * orthProd Q (List.ofFn h) =
      algebraMap F A ((-1 : F) ^ (n * (n - 1) / 2) * ∏ i, Q (h i)) := by
  rw [orthProd_sq_list _ (pairwise_ofFn_of_orth h horth), List.length_ofFn, Nat.choose_two_right,
    List.map_ofFn, List.prod_ofFn]
  rfl

/-- **Lemma 2.7 (ii)**, second formula (Shimura 2004, p. 19): $z^* = (-1)^{n(n-1)/2}z$. -/
@[kb "shimura2004" "Lemma 2.7 (ii), p. 19 (z* = (−1)^{n(n−1)/2} z)"]
theorem reverse_orthProd (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0) :
    reverse (orthProd Q (List.ofFn h)) = (-1 : F) ^ (n * (n - 1) / 2) • orthProd Q (List.ofFn h) := by
  rw [reverse_orthProd_list _ (pairwise_ofFn_of_orth h horth), List.length_ofFn, Nat.choose_two_right]

/-- **Lemma 2.7 (iv)**, the inclusion $F + Fz \subseteq$ center for $n$ odd (Shimura 2004, p. 19): if $n$ is odd,
$z$ commutes with every element of $A(V)$ (from (i)). -/
@[kb "shimura2004" "Lemma 2.7 (iv), p. 19 (n odd: z lies in the center of A(V))"]
theorem orthProd_mem_center_of_odd (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (hn : Odd n) (g : A) :
    orthProd Q (List.ofFn h) * g = g * orthProd Q (List.ofFn h) := by
  refine commute_of_commute_ι (fun x => ?_) g
  rw [vec_mul_orthProd h horth hspan x]
  obtain ⟨k, rfl⟩ := hn
  simp [pow_mul]

end OrthProd

end QuadFormsKB.Shimura2004

