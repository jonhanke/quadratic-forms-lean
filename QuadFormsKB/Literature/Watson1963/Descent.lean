/-
# Watson (1963), Theorem 3: a one-class genus does not represent certain perfect forms

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), §8, Theorem 3
(p. 563): *no positive form representing either of the perfect forms $\varphi_9$, $\Phi_9$ can have class-number $1$.*
Watson's proof uses only that the genus of $\varphi$ contains a form representing $E$ ($= E_8$). Here this is the
hypothesis that $\varphi$ represents $E_8$ over every $\mathbb Z_p$, for an arbitrary perfect form $\varphi$ with minimum
$1$ in $v > 8$ variables (`not_rep_of_oneClass`).

**Setting.** Forms of different numbers of variables are compared with `IsoOver S` (an isometry over the ring $S$,
`AppA/Watson.lean`), so that orthogonal sums can be regrouped without casts. A form $f$ *has one class*
(`OneClass`) if every form in its genus is integrally equivalent to it; for positive definite $f$ this is
`(genusClasses f).encard ≤ 1` (`oneClass_of_encard_le_one`).

**Proof (Watson's).** If $f$ has one class and represents $\varphi$, then $f$ represents $E_8$ over every $\mathbb Z_p$,
hence (one class, `OneClass.rep_of_local`) over $\mathbb Z$, so $E_8$ splits off (Lemma 5): $f \cong E_8 \perp \psi$, and
$\psi$ represents $\varphi$ (Lemma 3; $E_8$ has too few variables). Repeating with $\psi$ in place of $f$ (the genus of
$\psi$ contains a form $E_8 \perp \psi''$, and $f$ has one class) gives $f \cong E_8 \perp \dots \perp E_8 \perp \psi^{(k)}$
with $\psi^{(k)}$ still representing $\varphi$, which is impossible once $\psi^{(k)}$ has fewer than $v$ variables.
-/
import QuadFormsKB.Literature.Watson1963.GenusRep
import QuadFormsKB.Literature.Watson1963.Split
import QuadFormsKB.Literature.Watson1963.Probes

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n v : ℕ}

/-! ### Isometries between forms in possibly different numbers of variables -/

/-- Helper: a real isometry forces equal numbers of variables. -/
theorem _root_.QuadFormsKB.DefiniteForms.IsoOver.dim_eq {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} (h : IsoOver ℝ A B) : a = b := by
  obtain ⟨e, -⟩ := h
  have := e.finrank_eq
  simpa using this

/-- Helper: an integral isometry transports representations. -/
theorem Rep.of_isoOver {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} {φ : QuadForm ℤ v} (h : IsoOver ℤ A B)
    (hr : Rep A φ) : Rep B φ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨H, hH⟩ := hr
  refine ⟨LinearMap.toMatrix' (e.toLinearMap ∘ₗ Matrix.mulVecLin H), fun y => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Matrix.mulVecLin_apply]
  have := he (H *ᵥ y)
  simp only [QuadForm.eval] at hH ⊢
  rw [this]
  exact hH y

/-- Helper: an integral equivalence is an isometry over every ring. -/
theorem _root_.QuadFormsKB.DefiniteForms.IsoOver.of_intEquiv (S : Type*) [CommRing S] {A B : QuadForm ℤ n} (h : IntEquiv A B) : IsoOver S A B :=
  IsoOver.of_isometricGL (IsometricGL.map _ (IsometricGL.symm h))

/-- Helper: an isometry over $\mathbb Z$ in equal numbers of variables is an integral equivalence. -/
theorem _root_.QuadFormsKB.DefiniteForms.IsoOver.intEquiv {A B : QuadForm ℤ n} (h : IsoOver ℤ A B) : IntEquiv A B := by
  have := h.isometricGL
  have e : ∀ Q : QuadForm ℤ n, Q.map (Int.castRingHom ℤ) = Q := fun Q => by
    ext i j; simp [QuadForm.map]
  rwa [e, e] at this

/-- Helper: forms of the same genus are isometric over every $\mathbb Z_p$. -/
theorem _root_.QuadFormsKB.Siegel.SameGenus.isoOver_padic {A B : QuadForm ℤ n} (h : SameGenus A B) (p : ℕ) [Fact p.Prime] :
    IsoOver ℤ_[p] A B :=
  IsoOver.of_isometricGL (h.1 p).symm

/-- Helper: forms of the same genus are isometric over $\mathbb R$. -/
theorem _root_.QuadFormsKB.Siegel.SameGenus.isoOver_real {A B : QuadForm ℤ n} (h : SameGenus A B) : IsoOver ℝ A B :=
  IsoOver.of_isometricGL h.2.symm

/-- Helper: local isometries everywhere give the same genus (equal numbers of variables). -/
theorem sameGenus_of_isoOver {A B : QuadForm ℤ n} (hp : ∀ (p : ℕ) [Fact p.Prime], IsoOver ℤ_[p] A B)
    (hr : IsoOver ℝ A B) : SameGenus A B :=
  ⟨fun p _ => (hp p).isometricGL, hr.isometricGL⟩

/-- Helper: positive definiteness is invariant under real isometries. -/
theorem _root_.QuadFormsKB.IntQF.PosDef.of_isoOver_real {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} (hA : IntQF.PosDef A)
    (h : IsoOver ℝ A B) : IntQF.PosDef B := by
  obtain ⟨e, he⟩ := h
  intro y hy
  have hy' : (fun i => (y i : ℝ)) ≠ 0 := by
    intro h0; apply hy; funext i; have := congrFun h0 i; simpa using this
  have h1 : 0 < A.evalIn ℝ (e.symm fun i => (y i : ℝ)) :=
    hA.evalIn_real_pos _ (by simpa using hy')
  rw [← he, LinearEquiv.apply_symm_apply, evalIn_intCast_vec] at h1
  exact_mod_cast h1

/-- Helper: the second summand of a positive definite orthogonal sum is positive definite. -/
theorem _root_.QuadFormsKB.IntQF.PosDef.orthSum_right {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b}
    (h : IntQF.PosDef (QuadForm.orthSum A B)) : IntQF.PosDef B := by
  intro y hy
  have := h (Fin.append 0 y) (by
    intro h0; apply hy; funext j; have := congrFun h0 (Fin.natAdd a j); simpa using this)
  rw [eval_orthSum_int] at this
  have h0 : (fun i : Fin a => (Fin.append (0 : Fin a → ℤ) y) (Fin.castAdd b i)) = 0 := by
    funext i; simp
  have h1 : (fun j : Fin b => (Fin.append (0 : Fin a → ℤ) y) (Fin.natAdd a j)) = y := by
    funext j; simp
  rw [h0, h1, eval_zero_int, zero_add] at this
  exact this

/-! ### One class -/

/-- **One class in the genus** (Watson's $c(f) = 1$, §1): every form in the genus of $f$ is integrally equivalent to
$f$. Argument: the form `f`. -/
def OneClass (f : QuadForm ℤ n) : Prop := ∀ f' : QuadForm ℤ n, SameGenus f f' → IntEquiv f f'

/-- For a genus with at most one class, `OneClass` holds. -/
theorem oneClass_of_encard_le_one {f : QuadForm ℤ n} (h : (genusClasses f).encard ≤ 1) : OneClass f := by
  intro f' hf'
  have h1 : classOf f ∈ genusClasses f := classOf_self_mem_genusClasses f
  have h2 : classOf f' ∈ genusClasses f := classOf_mem_genusClasses_iff.mpr hf'
  have := Set.encard_le_one_iff.mp h _ _ h2 h1
  exact (classOf_eq_classOf_iff.mp this).symm

/-- **With one class, local representations are global** (Watson 1963, proofs of Lemma 12 and Theorem 3, from the
genus representation theorem `exists_sameGenus_rep`). -/
theorem OneClass.rep_of_local {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : OneClass f) (hf : IntQF.PosDef f)
    (hφ : IntQF.PosDef φ) (hloc : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] f φ) : Rep f φ := by
  obtain ⟨f', hg, hr⟩ := exists_sameGenus_rep hf hφ hloc
  exact Rep.of_intEquiv_left (IsometricGL.symm (h f' hg)) hr

/-- **One class, in any number of variables:** a form isometric to $f$ over $\mathbb R$ and every $\mathbb Z_p$ is
isometric to $f$ over $\mathbb Z$. -/
theorem OneClass.isoOver {f : QuadForm ℤ n} (h : OneClass f) {m : ℕ} {F : QuadForm ℤ m}
    (hp : ∀ (p : ℕ) [Fact p.Prime], IsoOver ℤ_[p] f F) (hr : IsoOver ℝ f F) : IsoOver ℤ f F := by
  obtain rfl := hr.dim_eq
  exact IsoOver.of_intEquiv ℤ (h F (sameGenus_of_isoOver hp hr))

/-! ### Theorem 3 -/

/-- Helper: the representations of a perfect form by an orthogonal sum one of whose summands cannot represent it. -/
theorem rep_right_of_perfect {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} {φ : QuadForm ℤ v}
    (hA : IntQF.PosDef A) (hB : IntQF.PosDef B) (hφ : IsPerfectOne φ) (hnA : ¬ Rep A φ)
    (h : Rep (QuadForm.orthSum A B) φ) : Rep B φ :=
  (rep_orthSum_of_perfect hA hB hφ h).resolve_left hnA

/-- Helper: an integral isometry forces equal numbers of variables. -/
theorem _root_.QuadFormsKB.DefiniteForms.IsoOver.dim_eq_int {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} (h : IsoOver ℤ A B) : a = b := by
  obtain ⟨e, -⟩ := h
  have := e.finrank_eq
  simpa using this

/-- Helper: an integral isometry gives an isometry over every ring. -/
theorem _root_.QuadFormsKB.DefiniteForms.IsoOver.baseChange (S : Type*) [CommRing S] {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b}
    (h : IsoOver ℤ A B) : IsoOver S A B := by
  obtain rfl := h.dim_eq_int
  exact IsoOver.of_intEquiv S h.intEquiv

/-- **The descent of Theorem 3** (Watson 1963, p. 563): let $f$ be positive definite with one class, and suppose
$f \cong A \perp \psi$ over $\mathbb Z$ where $A$ does not represent the perfect form $\varphi$ (in $v > 8$ variables,
representing $E_8$ over every $\mathbb Z_p$) and $\psi$ does. Contradiction, by induction on the number $m$ of
variables of $\psi$: $E_8$ splits off a form $\psi'$ of the genus of $\psi$, and $f \cong (A \perp E_8) \perp \psi''$
with $\psi''$ representing $\varphi$. -/
theorem descent_aux {f : QuadForm ℤ n} (h1 : OneClass f) {φ : QuadForm ℤ v}
    (hφ : IsPerfectOne φ) (hv : 8 < v) (hφE : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] φ formE8) :
    ∀ (m : ℕ) (a : ℕ) (A : QuadForm ℤ a) (ψ : QuadForm ℤ m), IntQF.PosDef A → IntQF.PosDef ψ → ¬ Rep A φ →
      Rep ψ φ → IsoOver ℤ f (QuadForm.orthSum A ψ) → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a A ψ hA hψ hnA hrep hiso
  -- ψ represents E8 locally, so a form ψ' of its genus represents E8
  have hψE : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] ψ formE8 := fun p _ =>
    (hrep.repOver ℤ_[p]).trans (hφE p)
  obtain ⟨ψ', hg, hrE⟩ := exists_sameGenus_rep hψ formE8_posDef hψE
  have hψ' : IntQF.PosDef ψ' := hψ.of_isoOver_real hg.isoOver_real
  obtain ⟨m'', hm, ψ'', hsplit⟩ :=
    exists_intEquiv_orthSum_of_rep (by rw [formE8_hessian_det]; exact isUnit_one) hrE
  subst hm
  have hsplit' : IsoOver ℤ ψ' (QuadForm.orthSum formE8 ψ'') := IsoOver.of_intEquiv ℤ hsplit
  have hS : ∀ (S : Type) [CommRing S], IsoOver S ψ ψ' →
      IsoOver S f (QuadForm.orthSum (QuadForm.orthSum A formE8) ψ'') := fun S _ hS =>
    ((hiso.baseChange S).trans ((IsoOver.refl A).orthSum (hS.trans (hsplit'.baseChange S)))).trans
      (IsoOver.assoc _ _ _)
  have hF : IsoOver ℤ f (QuadForm.orthSum (QuadForm.orthSum A formE8) ψ'') :=
    h1.isoOver (fun p _ => hS ℤ_[p] (hg.isoOver_padic p)) (hS ℝ hg.isoOver_real)
  have hrf : Rep (QuadForm.orthSum A ψ) φ := (Rep.orthSum_right A ψ).trans hrep
  have hrF : Rep (QuadForm.orthSum (QuadForm.orthSum A formE8) ψ'') φ :=
    Rep.of_isoOver hF (Rep.of_isoOver hiso.symm hrf)
  have hAE : IntQF.PosDef (QuadForm.orthSum A formE8) := posDef_orthSum hA formE8_posDef
  have hψ'' : IntQF.PosDef ψ'' := (hψ'.of_isoOver_real (hsplit'.baseChange ℝ)).orthSum_right
  have hnAE : ¬ Rep (QuadForm.orthSum A formE8) φ := by
    intro h
    rcases rep_orthSum_of_perfect hA formE8_posDef hφ h with h' | h'
    · exact hnA h'
    · exact hφ.not_rep_of_lt formE8 hv h'
  have hr'' : Rep ψ'' φ := rep_right_of_perfect hAE hψ'' hφ hnAE hrF
  exact ih m'' (by omega) _ _ ψ'' hAE hψ'' hnAE hr'' hF

/-- **Watson 1963, Theorem 3** (p. 563), in the form used: *a positive definite form with one class in its genus does
not represent a perfect form $\varphi$ with minimum $1$ in $v > 8$ variables that represents $E_8$ over every
$\mathbb Z_p$.* (Watson states it for $\varphi_9$ and $\Phi_9$, whose genera contain forms representing $E_8$.)
Arguments: `hf` positive definiteness, `h1` one class, `hφ` perfection, `hv : 8 < v`, `hφE` the local
representations of $E_8$ by $\varphi$. -/
@[kb "watson1963" "§8, Theorem 3, p. 563"]
theorem not_rep_of_oneClass {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (h1 : OneClass f) {φ : QuadForm ℤ v}
    (hφ : IsPerfectOne φ) (hv : 8 < v) (hφE : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] φ formE8) :
    ¬ Rep f φ := by
  intro hr
  have hE : Rep f formE8 := h1.rep_of_local hf formE8_posDef fun p _ => (hr.repOver ℤ_[p]).trans (hφE p)
  obtain ⟨m, hm, ψ, hsplit⟩ :=
    exists_intEquiv_orthSum_of_rep (by rw [formE8_hessian_det]; exact isUnit_one) hE
  subst hm
  have hiso : IsoOver ℤ f (QuadForm.orthSum formE8 ψ) := IsoOver.of_intEquiv ℤ hsplit
  have hψ : IntQF.PosDef ψ := (hf.of_isoOver_real (hiso.baseChange ℝ)).orthSum_right
  have hr' : Rep (QuadForm.orthSum formE8 ψ) φ := Rep.of_isoOver hiso hr
  have hnE : ¬ Rep formE8 φ := hφ.not_rep_of_lt formE8 hv
  exact descent_aux h1 hφ hv hφE m 8 formE8 ψ formE8_posDef hψ hnE
    (rep_right_of_perfect formE8_posDef hψ hφ hnE hr') hiso

end QuadFormsKB.Watson1963
