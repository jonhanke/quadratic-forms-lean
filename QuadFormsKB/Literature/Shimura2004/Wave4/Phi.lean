/-
# Shimura 2004, §3.14: the splitting $V = F\kappa \oplus W$ and the map $\Phi : A(V) \to M_2(A(W))$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §3.14,
formulas (3.16)–(3.19) (printed p. 26). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `QuadFormsKB/Literature/Shimura2004/Wave4/MatrixModel.lean`: $F$ a field of
characteristic $\ne 2$, `Q : QuadraticForm F V`, a weak Witt decomposition $V = U + Fe + Ff$ with `Q e = 0`,
`Q f = 0`, `QuadraticMap.polar Q e f = 1` ($ef + fe = 1$), $U$ = `uSpace Q e f`, $\Psi$ = `psi`. Put
$\kappa = e + f$ and $\ell = e - f$ (Shimura writes $\iota$ for $\ell$; we write `ell`/$\ell$ to avoid a clash with
Mathlib's `ι`). Then $\kappa^2 = 1$, $\ell^2 = -1$, $\kappa\ell = -\ell\kappa$, and $V = F\kappa \oplus W$ with
$W = (F\kappa)^\perp$ = `wSpace Q e f`. $A(W)$ = `AW Q e f` is the Clifford algebra of $\varphi|_W$, mapped into
$A(V)$ by `inclW`; $A(U) \to A(W)$ is `inclUW`.

**Defines**
* $W = (F\kappa)^\perp$ (`wSpace`), $A(W)$ (`AW`), `inclW`, `inclUW`;
* (3.18) $\Phi : A(V) \to M_2(A(W))$, the $F$-algebra homomorphism with
  $\Phi(w + t\kappa) = \begin{pmatrix} w & t \\ t & -w\end{pmatrix}$ for $w \in W$, $t \in F$ (`phi`);
* (3.19) $R = \begin{pmatrix} 1 & \ell \\ \ell & 1\end{pmatrix}$ (`matR`) and $R^{-1} = \tfrac12
  \begin{pmatrix} 1 & -\ell \\ -\ell & 1\end{pmatrix}$ (`matRinv`).

**Proves** (all unconditional; standard axioms only)
* $\kappa^2 = 1$, $\ell^2 = -1$, $\kappa\ell = -\ell\kappa$, $\ell \in W$, $U \subseteq W$;
* (3.16) $W = U \oplus F\ell$ (`wSpace_decomp`) and $U = \{v \in W : \ell v = -v\ell\}$
  (`mem_uSpace_iff_anticomm`);
* (3.17) $\Psi(\kappa) = \begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$, $\Psi(\ell) = \begin{pmatrix} 0 & 1 \\ -1 & 0
  \end{pmatrix}$ (`psi_kappa`, `psi_ell`);
* (3.18) $\Phi(p + \kappa q) = \begin{pmatrix} p & q' \\ q & p'\end{pmatrix}$ for $p, q \in A(W)$ (`phi_formula`),
  every element of $A(V)$ has this form (`exists_inclW`), and $\Phi$ is injective (`phi_injective`);
* (3.19) $\Psi(\alpha) = R\,\Phi(\alpha)\,R^{-1}$ in $M_2(A(W))$, with $A(U)$ viewed in $A(W)$ (`psi_eq_conj_phi`),
  and $RR^{-1} = R^{-1}R = 1$ (`matR_mul_matRinv`, `matRinv_mul_matR`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.MatrixModel
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace MatrixModel

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (Q : QuadraticForm F V) (e f : V)

/-! ### The space $W = (F\kappa)^\perp$ and its Clifford algebra -/

/-- **Shimura's $W = (F\kappa)^\perp$** (§3.14, p. 26), $\kappa = e + f$: the vectors $w$ with
$\varphi(w, \kappa) = 0$ (stated with $2\varphi$ = `QuadraticMap.polar Q`). -/
@[kb "shimura2004" "§3.14, p. 26 (W = (Fκ)^⊥, κ = e + f)"]
def wSpace : Submodule F V :=
  LinearMap.ker ((QuadraticMap.polarBilin Q).flip (e + f))

variable {Q e f} in
theorem mem_wSpace {w : V} : w ∈ wSpace Q e f ↔ QuadraticMap.polar Q w (e + f) = 0 := by
  simp [wSpace, QuadraticMap.polarBilin]

/-- The quadratic form $\varphi$ restricted to $W$. -/
abbrev QW : QuadraticForm F (wSpace Q e f) := Q.restrict (wSpace Q e f)

/-- **Shimura's $A(W)$**: the Clifford algebra of $\varphi$ restricted to $W$. -/
abbrev AW := CliffordAlgebra (QW Q e f)

/-- The inclusion $W \subseteq V$ as an isometry. -/
def inclIsoW : (QW Q e f) →qᵢ Q where
  toLinearMap := (wSpace Q e f).subtype
  map_app' _ := rfl

/-- The map $A(W) \to A(V)$ induced by $W \subseteq V$. -/
def inclW : AW Q e f →ₐ[F] CliffordAlgebra Q := CliffordAlgebra.map (inclIsoW Q e f)

@[simp] theorem inclW_ι (w : wSpace Q e f) : inclW Q e f (ι (QW Q e f) w) = ι Q (w : V) := by
  rw [inclW, CliffordAlgebra.map_apply_ι]; rfl

variable {Q e f} in
theorem uSpace_le_wSpace : uSpace Q e f ≤ wSpace Q e f := by
  intro u hu
  rw [mem_uSpace] at hu
  rw [mem_wSpace, QuadraticMap.polar_add_right, hu.1, hu.2, add_zero]

/-- The isometry $U \to W$ induced by $U \subseteq W$. -/
def inclIsoUW : (QU Q e f) →qᵢ (QW Q e f) where
  toLinearMap := Submodule.inclusion (uSpace_le_wSpace (Q := Q) (e := e) (f := f))
  map_app' _ := rfl

/-- The map $A(U) \to A(W)$ induced by $U \subseteq W$. -/
def inclUW : AU Q e f →ₐ[F] AW Q e f := CliffordAlgebra.map (inclIsoUW Q e f)

@[simp] theorem inclUW_ι (u : uSpace Q e f) :
    inclUW Q e f (ι (QU Q e f) u) = ι (QW Q e f) ⟨(u : V), uSpace_le_wSpace u.2⟩ := by
  rw [inclUW, CliffordAlgebra.map_apply_ι]; rfl

/-- The linear form $x \mapsto \varphi(x, \kappa) = \tfrac12\,\mathrm{polar}(x, \kappa)$ (the coefficient $t$ of
$\kappa$ in $x = w + t\kappa$). -/
def tfun : V →ₗ[F] F := (⅟2 : F) • ((QuadraticMap.polarBilin Q).flip (e + f))

theorem tfun_apply (x : V) : tfun Q e f x = ⅟2 * QuadraticMap.polar Q x (e + f) := by
  simp [tfun, QuadraticMap.polarBilin, mul_add]

variable {Q e f}

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)
include he hf hef

/-- $\varphi[\kappa] = 1$, i.e. $\kappa^2 = 1$. -/
theorem Q_kappa : Q (e + f) = 1 := by
  rw [QuadraticMap.map_add (⇑Q), he, hf, hef]; ring

/-- $\varphi[\ell] = -1$, i.e. $\ell^2 = -1$. -/
theorem Q_ell : Q (e - f) = -1 := by
  rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q), QuadraticMap.map_neg, he, hf,
    QuadraticMap.polar_neg_right, hef]
  ring

theorem polar_kappa_kappa : QuadraticMap.polar Q (e + f) (e + f) = 2 := by
  rw [QuadraticMap.polar_self, Q_kappa he hf hef]; simp

theorem polar_ell_kappa : QuadraticMap.polar Q (e - f) (e + f) = 0 := by
  simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_add_right, polar_e_e he hf hef,
    polar_f_f he hf hef, hef, polar_f_e he hf hef]
  ring

/-- $\ell \in W$. -/
theorem ell_mem : (e - f) ∈ wSpace Q e f := mem_wSpace.2 (polar_ell_kappa he hf hef)

/-- $\ell$ as an element of $W$. -/
def ellW : wSpace Q e f := ⟨e - f, ell_mem he hf hef⟩

/-- $\kappa^2 = 1$ in $A(V)$. -/
theorem ι_kappa_sq : ι Q (e + f) * ι Q (e + f) = 1 := by
  rw [ι_sq_scalar, Q_kappa he hf hef, map_one]

/-- $\ell^2 = -1$ in $A(V)$. -/
theorem ι_ell_sq : ι Q (e - f) * ι Q (e - f) = -1 := by
  rw [ι_sq_scalar, Q_ell he hf hef, map_neg, map_one]

/-- $\kappa\ell = -\ell\kappa$ in $A(V)$. -/
theorem ι_kappa_ell : ι Q (e + f) * ι Q (e - f) = -(ι Q (e - f) * ι Q (e + f)) := by
  rw [eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, QuadraticMap.polar_comm, polar_ell_kappa he hf hef, map_zero]

/-- $\ell^2 = -1$ in $A(W)$. -/
theorem ι_ellW_sq : ι (QW Q e f) (ellW he hf hef) * ι (QW Q e f) (ellW he hf hef) = -1 := by
  rw [ι_sq_scalar]
  change algebraMap F _ (Q (e - f)) = _
  rw [Q_ell he hf hef, map_neg, map_one]

/-! ### (3.16) -/

/-- **(3.16)**, p. 26: $W = U \oplus F\ell$: every $w \in W$ is uniquely $u + t\ell$ with $u \in U$, $t \in F$
(namely $t = 2\varphi(w, f)$). -/
@[kb "shimura2004" "(3.16), p. 26 (W = U ⊕ Fι, ι = e − f)"]
theorem wSpace_decomp {w : V} (hw : w ∈ wSpace Q e f) :
    ∃! p : V × F, p.1 ∈ uSpace Q e f ∧ w = p.1 + p.2 • (e - f) := by
  have h1 := polar_e_e he hf hef
  have h2 := polar_f_f he hf hef
  have h3 := polar_f_e he hf hef
  rw [mem_wSpace, QuadraticMap.polar_add_right] at hw
  refine ⟨(w - QuadraticMap.polar Q w f • (e - f), QuadraticMap.polar Q w f), ⟨?_, by simp⟩, ?_⟩
  · rw [mem_uSpace]
    constructor
    · simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul, h1, h3]
      linear_combination hw
    · simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul, h2, hef]
      ring
  · rintro ⟨u', t'⟩ ⟨hu', hw'⟩
    rw [mem_uSpace] at hu'
    have ht : t' = QuadraticMap.polar Q w f := by
      have := congrArg (fun z => QuadraticMap.polar Q z f) hw'
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_sub_left,
        smul_eq_mul, hu'.2, h2, hef] at this
      linear_combination -this
    subst ht
    refine Prod.ext ?_ rfl
    show u' = w - _ • _
    rw [eq_sub_iff_add_eq]; exact hw'.symm

/-- **(3.16)**, p. 26: for $v \in W$, $v \in U$ iff $\ell v = -v\ell$. -/
@[kb "shimura2004" "(3.16), p. 26 (U = {v ∈ W | ιv = −vι})"]
theorem mem_uSpace_iff_anticomm {v : V} (hv : v ∈ wSpace Q e f) :
    v ∈ uSpace Q e f ↔ ι Q (e - f) * ι Q v = -(ι Q v * ι Q (e - f)) := by
  rw [eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, map_eq_zero_iff _ (algebraMap F _).injective,
    mem_uSpace]
  rw [mem_wSpace, QuadraticMap.polar_add_right] at hv
  have hpol : QuadraticMap.polar Q (e - f) v = QuadraticMap.polar Q v e - QuadraticMap.polar Q v f := by
    rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_comm Q e v, QuadraticMap.polar_comm Q f v]
  rw [hpol]
  generalize QuadraticMap.polar Q v e = a at *
  generalize QuadraticMap.polar Q v f = b at *
  constructor
  · rintro ⟨rfl, rfl⟩; simp
  · intro h
    have ha : a = 0 := by
      have : (2 : F) * a = 0 := by linear_combination hv + h
      calc a = ⅟2 * (2 * a) := (invOf_mul_cancel_left 2 a).symm
        _ = 0 := by rw [this, mul_zero]
    refine ⟨ha, ?_⟩
    rw [ha] at hv; simpa using hv

/-! ### (3.17) -/

/-- **(3.17)**, p. 26: $\Psi(\kappa) = \begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$. -/
@[kb "shimura2004" "(3.17), p. 26 (Ψ(κ) = [[0, 1], [1, 0]])"]
theorem psi_kappa : psi he hf hef (ι Q (e + f)) = !![0, 1; 1, 0] := by
  rw [map_add (ι Q), map_add, psi_e, psi_f]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **(3.17)**, p. 26: $\Psi(\ell) = \begin{pmatrix} 0 & 1 \\ -1 & 0\end{pmatrix}$. -/
@[kb "shimura2004" "(3.17), p. 26 (Ψ(ι) = [[0, 1], [−1, 0]])"]
theorem psi_ell : psi he hf hef (ι Q (e - f)) = !![0, 1; -1, 0] := by
  rw [map_sub (ι Q), map_sub, psi_e, psi_f]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### (3.18): the map $\Phi$ -/

theorem projW_mem (x : V) : x - tfun Q e f x • (e + f) ∈ wSpace Q e f := by
  rw [mem_wSpace]
  simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul,
    polar_kappa_kappa he hf hef, tfun_apply]
  have : (⅟2 : F) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(QuadraticMap.polar Q x (e + f))) * this

/-- The $W$-component $x - t\kappa$ of $x = w + t\kappa$. -/
def projW : V →ₗ[F] wSpace Q e f :=
  (LinearMap.id - (tfun Q e f).smulRight (e + f)).codRestrict (wSpace Q e f)
    (fun x => projW_mem he hf hef x)

theorem coe_projW (x : V) : (projW he hf hef x : V) = x - tfun Q e f x • (e + f) := rfl

/-- Every $x \in V$ is $w + t\kappa$ with $w$ = `projW x` $\in W$ and $t = \varphi(x, \kappa)$. -/
theorem decompW (x : V) : x = (projW he hf hef x : V) + tfun Q e f x • (e + f) := by
  rw [coe_projW]; abel

theorem tfun_kappa : tfun Q e f (e + f) = 1 := by
  rw [tfun_apply, polar_kappa_kappa he hf hef]; exact invOf_mul_self 2

omit he hf hef in
theorem tfun_of_mem {w : V} (hw : w ∈ wSpace Q e f) : tfun Q e f w = 0 := by
  rw [tfun_apply, mem_wSpace.1 hw, mul_zero]

theorem projW_of_mem {w : V} (hw : w ∈ wSpace Q e f) : (projW he hf hef w : V) = w := by
  rw [coe_projW, tfun_of_mem hw, zero_smul, sub_zero]

theorem projW_kappa : (projW he hf hef (e + f) : V) = 0 := by
  rw [coe_projW, tfun_kappa he hf hef, one_smul, sub_self]

/-- $\varphi[w + t\kappa] = \varphi[w] + t^2$. -/
theorem Q_eq_projW_add (x : V) :
    Q x = Q (projW he hf hef x : V) + tfun Q e f x * tfun Q e f x := by
  have hw := (projW he hf hef x).2
  rw [mem_wSpace] at hw
  conv_lhs => rw [decompW he hf hef x]
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.polar_smul_right, hw,
    Q_kappa he hf hef]
  simp [smul_eq_mul]

/-- **Shimura's $\Phi$ on $V$** (3.18): $\Phi(w + t\kappa) = \begin{pmatrix} w & t \\ t & -w\end{pmatrix}$. -/
def phiVec : V →ₗ[F] Matrix (Fin 2) (Fin 2) (AW Q e f) where
  toFun x := !![ι (QW Q e f) (projW he hf hef x), algebraMap F _ (tfun Q e f x);
    algebraMap F _ (tfun Q e f x), -ι (QW Q e f) (projW he hf hef x)]
  map_add' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [map_add] <;> abel
  map_smul' c x := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Algebra.smul_def]

theorem phiVec_apply (x : V) : phiVec he hf hef x =
    !![ι (QW Q e f) (projW he hf hef x), algebraMap F _ (tfun Q e f x);
      algebraMap F _ (tfun Q e f x), -ι (QW Q e f) (projW he hf hef x)] := rfl

theorem phiVec_sq (x : V) :
    phiVec he hf hef x * phiVec he hf hef x = algebraMap F _ (Q x) := by
  rw [phiVec_apply, Matrix.mul_fin_two, Q_eq_projW_add he hf hef x]
  have h1 : ι (QW Q e f) (projW he hf hef x) * ι (QW Q e f) (projW he hf hef x) =
      algebraMap F _ (Q (projW he hf hef x : V)) := by
    rw [ι_sq_scalar]; rfl
  set t := tfun Q e f x
  set w := ι (QW Q e f) (projW he hf hef x)
  have hc : algebraMap F (AW Q e f) t * w = w * algebraMap F (AW Q e f) t := Algebra.commutes t w
  rw [Matrix.algebraMap_eq_diagonal]
  ext i j; fin_cases i <;> fin_cases j
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Matrix.diagonal_apply_eq, h1]
    rw [Pi.algebraMap_apply, map_add, map_mul]
  · simp [hc]
  · simp [hc]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue, Matrix.diagonal_apply_eq,
      neg_mul_neg, h1]
    rw [Pi.algebraMap_apply, map_add, map_mul, add_comm]

/-- **Shimura's $\Phi : A(V) \to M_2(A(W))$** (3.18), p. 26: the extension of
$\Phi(w + t\kappa) = \begin{pmatrix} w & t \\ t & -w\end{pmatrix}$ to an $F$-algebra homomorphism (possible since
$\Phi(x)^2 = \varphi[x]1_2$). It is injective (`phi_injective`). -/
@[kb "shimura2004" "(3.18), p. 26 (Φ : A(V) → M₂(A(W)), Φ(p + κq) = [[p, q'], [q, p']])"]
def phi : CliffordAlgebra Q →ₐ[F] Matrix (Fin 2) (Fin 2) (AW Q e f) :=
  CliffordAlgebra.lift Q ⟨phiVec he hf hef, phiVec_sq he hf hef⟩

theorem phi_ι (x : V) : phi he hf hef (ι Q x) = phiVec he hf hef x := by
  simp [phi]

/-- $\Phi(w) = \mathrm{diag}[w, -w]$ for $w \in W$. -/
theorem phi_ι_of_mem (w : wSpace Q e f) :
    phi he hf hef (ι Q (w : V)) = !![ι (QW Q e f) w, 0; 0, -ι (QW Q e f) w] := by
  have hp : projW he hf hef (w : V) = w := Subtype.ext (projW_of_mem he hf hef w.2)
  rw [phi_ι, phiVec_apply, hp, tfun_of_mem w.2, map_zero]

/-- $\Phi(\kappa) = \begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$. -/
theorem phi_kappa : phi he hf hef (ι Q (e + f)) = !![0, 1; 1, 0] := by
  have hp : projW he hf hef (e + f) = 0 := Subtype.ext (projW_kappa he hf hef)
  rw [phi_ι, phiVec_apply, hp, tfun_kappa he hf hef]
  simp

/-- $\Phi(b) = \mathrm{diag}[b, b']$ for $b \in A(W)$. -/
theorem phi_inclW (b : AW Q e f) : phi he hf hef (inclW Q e f b) = !![b, 0; 0, involute b] := by
  induction b using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Pi.algebraMap_apply]
  | ι w => rw [inclW_ι, phi_ι_of_mem, involute_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, Matrix.mul_fin_two, map_mul]; simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]; ext i j; fin_cases i <;> fin_cases j <;> simp

omit he hf hef in
/-- $\kappa b = b'\kappa$ for $b \in A(W)$ (as $\kappa \perp W$). -/
theorem ι_kappa_mul_inclW (b : AW Q e f) :
    ι Q (e + f) * inclW Q e f b = inclW Q e f (involute b) * ι Q (e + f) := by
  induction b using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι w =>
    have hw := mem_wSpace.1 w.2
    rw [inclW_ι, involute_ι, map_neg, inclW_ι, neg_mul, eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap,
      QuadraticMap.polar_comm, hw, map_zero]
  | mul a b ha hb => rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc, map_mul, map_mul]
  | add a b ha hb =>
    rw [map_add (inclW Q e f) a b, mul_add, ha, hb, map_add (involute : CliffordAlgebra (QW Q e f) →ₐ[F] _) a b,
      map_add (inclW Q e f), add_mul]

/-- **(3.18)**, p. 26: $\Phi(p + \kappa q) = \begin{pmatrix} p & q' \\ q & p'\end{pmatrix}$ for $p, q \in A(W)$. -/
@[kb "shimura2004" "(3.18), p. 26 (Φ(p + κq) = [[p, q'], [q, p']] for p, q ∈ A(W))"]
theorem phi_formula (p q : AW Q e f) :
    phi he hf hef (inclW Q e f p + ι Q (e + f) * inclW Q e f q) =
      !![p, involute q; q, involute p] := by
  rw [map_add, map_mul, phi_kappa, phi_inclW, phi_inclW]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]

/-- **(3.18)**, p. 26: every element of $A(V)$ is $p + \kappa q$ with $p, q \in A(W)$. -/
@[kb "shimura2004" "(3.18), p. 26 (A(V) = A(W) + κA(W))"]
theorem exists_inclW (α : CliffordAlgebra Q) :
    ∃ p q : AW Q e f, α = inclW Q e f p + ι Q (e + f) * inclW Q e f q := by
  induction α using CliffordAlgebra.left_induction with
  | algebraMap r => exact ⟨algebraMap F _ r, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [map_add, mul_add]; abel⟩
  | ι_mul x v hx =>
    obtain ⟨p, q, rfl⟩ := hx
    set w := projW he hf hef v
    set t := tfun Q e f v
    have hv : ι Q v = ι Q (w : V) + t • ι Q (e + f) := by
      rw [← map_smul, ← map_add, ← decompW he hf hef v]
    have hwk : ι Q (w : V) * ι Q (e + f) = -(ι Q (e + f) * ι Q (w : V)) := by
      rw [eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, mem_wSpace.1 w.2, map_zero]
    have hkk := ι_kappa_sq he hf hef
    set K := ι Q (e + f)
    refine ⟨ι (QW Q e f) w * p + t • q, t • p - ι (QW Q e f) w * q, ?_⟩
    simp only [hv, map_add, map_sub, map_mul, map_smul, inclW_ι, mul_sub, mul_add, add_mul, smul_mul_assoc,
      mul_smul_comm, ← mul_assoc, hwk, hkk, neg_mul, one_mul, smul_add, smul_sub]
    simp only [mul_assoc, smul_neg]
    abel

theorem eq_inclW_phi (α : CliffordAlgebra Q) :
    α = inclW Q e f (phi he hf hef α 0 0) + ι Q (e + f) * inclW Q e f (phi he hf hef α 1 0) := by
  obtain ⟨p, q, rfl⟩ := exists_inclW he hf hef α
  rw [phi_formula]
  simp

/-- **(3.18)**, p. 26: $\Phi$ is injective (a ring injection). -/
@[kb "shimura2004" "(3.18), p. 26 (Φ is a ring injection A(V) → M₂(A(W)))"]
theorem phi_injective : Function.Injective (phi he hf hef) := by
  intro α β h
  rw [eq_inclW_phi he hf hef α, eq_inclW_phi he hf hef β, h]

/-! ### (3.19): Psi = R Phi R^(-1) -/

/-- The vector ell = e - f as an element of A(W). -/
abbrev ellA : AW Q e f := ι (QW Q e f) (ellW he hf hef)

/-- **Shimura's R** (3.19), p. 26: the matrix with rows (1, ell), (ell, 1) over A(W). -/
def matR : Matrix (Fin 2) (Fin 2) (AW Q e f) := !![1, ellA he hf hef; ellA he hf hef, 1]

/-- **Shimura's R inverse** (3.19), p. 26: one half of the matrix with rows (1, -ell), (-ell, 1)
(see `matR_mul_matRinv`, `matRinv_mul_matR`). -/
def matRinv : Matrix (Fin 2) (Fin 2) (AW Q e f) :=
  (⅟2 : F) • !![1, -ellA he hf hef; -ellA he hf hef, 1]

/-- R times R inverse is 1. -/
@[kb "shimura2004" "(3.19), p. 26 (R = [[1, ι], [ι, 1]] is invertible)"]
theorem matR_mul_matRinv : matR he hf hef * matRinv he hf hef = 1 := by
  have hsq := ι_ellW_sq he hf hef
  have h : matR he hf hef * !![1, -ellA he hf hef; -ellA he hf hef, 1] =
      (2 : F) • (1 : Matrix (Fin 2) (Fin 2) (AW Q e f)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [matR, Matrix.mul_apply, Fin.sum_univ_two, hsq, Matrix.one_apply, two_smul] <;> abel
  rw [matRinv, Matrix.mul_smul, h, smul_smul, invOf_mul_self, one_smul]

/-- R inverse times R is 1. -/
theorem matRinv_mul_matR : matRinv he hf hef * matR he hf hef = 1 := by
  have hsq := ι_ellW_sq he hf hef
  have h : !![1, -ellA he hf hef; -ellA he hf hef, 1] * matR he hf hef =
      (2 : F) • (1 : Matrix (Fin 2) (Fin 2) (AW Q e f)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [matR, Matrix.mul_apply, Fin.sum_univ_two, hsq, Matrix.one_apply, two_smul] <;> abel
  rw [matRinv, Matrix.smul_mul, h, smul_smul, invOf_mul_self, one_smul]

/-- A vector u of U anticommutes with ell in A(W). -/
theorem ι_ellA_anticomm (u : uSpace Q e f) :
    ellA he hf hef * ι (QW Q e f) ⟨(u : V), uSpace_le_wSpace u.2⟩ =
      -(ι (QW Q e f) ⟨(u : V), uSpace_le_wSpace u.2⟩ * ellA he hf hef) := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ι_mul_ι_add_swap, map_eq_zero_iff _ (algebraMap F _).injective]
  change QuadraticMap.polar Q (u : V) (e - f) = 0
  rw [QuadraticMap.polar_sub_right, (mem_uSpace.1 u.2).1, (mem_uSpace.1 u.2).2, sub_zero]

section Conj

local notation "ξ" => (AlgHom.mapMatrix (inclUW Q e f) :
  Matrix (Fin 2) (Fin 2) (AU Q e f) →ₐ[F] Matrix (Fin 2) (Fin 2) (AW Q e f))

theorem psiVec_mul_R_U (u : uSpace Q e f) :
    ξ (psiVec he hf hef (u : V)) * matR he hf hef = matR he hf hef * phiVec he hf hef (u : V) := by
  have h1 := ι_ellA_anticomm he hf hef u
  rw [← psi_ι, ← phi_ι, psi_ι_of_mem, phi_ι_of_mem he hf hef ⟨(u : V), uSpace_le_wSpace u.2⟩]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matR, Matrix.mul_apply, Fin.sum_univ_two, AlgHom.mapMatrix_apply, h1]

theorem psiVec_mul_R_kappa :
    ξ (psiVec he hf hef (e + f)) * matR he hf hef = matR he hf hef * phiVec he hf hef (e + f) := by
  rw [← psi_ι, ← phi_ι, psi_kappa, phi_kappa]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matR, Matrix.mul_apply, Fin.sum_univ_two, AlgHom.mapMatrix_apply]

theorem psiVec_mul_R_ell :
    ξ (psiVec he hf hef (e - f)) * matR he hf hef = matR he hf hef * phiVec he hf hef (e - f) := by
  have hsq := ι_ellW_sq he hf hef
  have hp : phi he hf hef (ι Q (e - f)) = !![ellA he hf hef, 0; 0, -ellA he hf hef] :=
    phi_ι_of_mem he hf hef (ellW he hf hef)
  rw [← psi_ι, ← phi_ι, psi_ell, hp]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matR, Matrix.mul_apply, Fin.sum_univ_two, AlgHom.mapMatrix_apply, hsq]

theorem psiVec_mul_R (v : V) :
    ξ (psiVec he hf hef v) * matR he hf hef = matR he hf hef * phiVec he hf hef v := by
  set u := proj he hf hef v
  set r := QuadraticMap.polar Q v f
  set s := QuadraticMap.polar Q v e
  have h2 : (⅟2 : F) * 2 = 1 := invOf_mul_self 2
  have hdec : v = (u : V) + (⅟2 * (r + s)) • (e + f) + (⅟2 * (r - s)) • (e - f) := by
    conv_lhs => rw [decomp he hf hef v]
    match_scalars <;> first | ring1 | linear_combination (-r) * h2 | linear_combination (-s) * h2
  have hU := psiVec_mul_R_U he hf hef u
  have hK := psiVec_mul_R_kappa he hf hef
  have hL := psiVec_mul_R_ell he hf hef
  rw [hdec]
  generalize e + f = K at *
  generalize e - f = L at *
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hU, hK, hL]

theorem psi_mul_R (α : CliffordAlgebra Q) :
    ξ (psi he hf hef α) * matR he hf hef = matR he hf hef * phi he hf hef α := by
  induction α using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]; exact Algebra.commutes r (matR he hf hef)
  | ι v => rw [psi_ι, phi_ι]; exact psiVec_mul_R he hf hef v
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [map_add, map_add, map_add, add_mul, mul_add, ha, hb]

/-- **(3.19)**, p. 26: Psi(alpha) = R Phi(alpha) R^(-1) as matrices over A(W), where the entries of
Psi(alpha) in M_2(A(U)) are mapped into A(W) by `inclUW`. -/
@[kb "shimura2004" "(3.19), p. 26 (Ψ(α) = RΦ(α)R⁻¹, R = [[1, ι], [ι, 1]])"]
theorem psi_eq_conj_phi (α : CliffordAlgebra Q) :
    (psi he hf hef α).map (inclUW Q e f) = matR he hf hef * phi he hf hef α * matRinv he hf hef := by
  calc (psi he hf hef α).map (inclUW Q e f)
      = ξ (psi he hf hef α) * (matR he hf hef * matRinv he hf hef) := by
        rw [matR_mul_matRinv, mul_one]; rfl
    _ = ξ (psi he hf hef α) * matR he hf hef * matRinv he hf hef := by rw [mul_assoc]
    _ = _ := by rw [psi_mul_R]

end Conj

end Hyp

end MatrixModel

end QuadFormsKB.Shimura2004
