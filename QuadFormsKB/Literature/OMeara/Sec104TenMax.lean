/-
# O'Meara Theorem 104:10, the maximal case: maximal lattices of the same norm are in one genus

**Layer:** $V = F^n$ over a number field $F$, `Q : QuadForm F n` nondegenerate, lattices `Lat F n`.

**Proves** (O'Meara 1973, proof of Theorem 104:10, pp. 320–321: "In the maximal case we note that both $L$ and $K$
must be $\mathfrak a$-maximal where $\mathfrak a$ is the common norm $\mathfrak a = \mathfrak nL = \mathfrak nK$, hence
$\operatorname{gen}L = \operatorname{gen}K$ by Theorem 91:2")
* `exists_mem_Q_ne_zero`, `normIdeal_ne_bot`: a lattice on a regular space of positive dimension has a non-zero norm;
* `isMaximal_normIdeal`: an $\mathfrak a$-maximal lattice is $\mathfrak nL$-maximal;
* `sameGenus_of_isMaximalLat`: two maximal lattices on $V$ with the same norm are in the same genus.
-/
import QuadFormsKB.Literature.OMeara.Sec102Three

open NumberField IsDedekindDomain Matrix Submodule
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **A lattice on a regular space contains an anisotropic vector**: for $Q$ nondegenerate on $F^n$, $n \ge 1$, every
lattice $L$ on $F^n$ contains some $x$ with $Q(x) \ne 0$. *Proof:* otherwise the polar form
$x \cdot Hy = Q(x + y) - Q(x) - Q(y)$ vanishes on $L \times L$, hence on $F^n \times F^n$ ($L$ spans $F^n$), so the
Hessian $H$ is $0$, contradicting $\det H \ne 0$. -/
theorem exists_mem_Q_ne_zero (hQ : Q.Nondegenerate) (hn : 0 < n) (L : Lat F n) :
    ∃ x ∈ L.1, Q.toQuadraticForm x ≠ 0 := by
  by_contra h
  push Not at h
  set H := Q.hessian.map (algebraMap F F) with hH
  have hHe : H = Q.hessian := by rw [hH]; ext i j; simp
  have hpol : ∀ x ∈ L.1, ∀ y ∈ L.1, Matrix.toBilin' H x y = 0 := by
    intro x hx y hy
    have e := QuadForm.polar_eq_hessian F Q x y
    have h1 := h (x + y) (L.1.add_mem hx hy)
    have h2 := h x hx
    have h3 := h y hy
    rw [QuadForm.toQuadraticForm_apply, QuadForm.eval] at h1 h2 h3
    rw [Matrix.toBilin'_apply', hH, ← e]
    rw [h1, h2, h3]; ring
  have hspan : span F (L.1 : Set (Fin n → F)) = ⊤ := L.2.span_eq_top
  have hB : Matrix.toBilin' H = 0 := by
    refine LinearMap.ext_on hspan fun x hx => ?_
    refine LinearMap.ext_on hspan fun y hy => ?_
    simpa using hpol x hx y hy
  have hH0 : H = 0 := by
    have := congrArg (LinearMap.BilinForm.toMatrix' (R₁ := F)) hB
    simpa using this
  have : Q.hessian.det = 0 := by
    rw [← hHe, hH0]
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Matrix.det_zero
  exact hQ this

/-- **The norm of a lattice on a regular space is non-zero**: for $Q$ nondegenerate on $F^n$, $n \ge 1$, and a lattice
$L$ on $F^n$, $\mathfrak nL \ne 0$. -/
theorem normIdeal_ne_bot (hQ : Q.Nondegenerate) (hn : 0 < n) (L : Lat F n) :
    OMeara.normIdeal Q.toQuadraticForm L.1 ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_Q_ne_zero Q hQ hn L
  intro h
  have := OMeara.Q_mem_normIdeal Q.toQuadraticForm hx
  rw [h, mem_bot] at this
  exact hx0 this

/-- **An $\mathfrak a$-maximal lattice is $\mathfrak nL$-maximal** (O'Meara 1973, proof of Theorem 104:10, p. 321): if
$L$ is $\mathfrak a$-maximal then it is maximal among the lattices of norm contained in $\mathfrak nL$ (since
$\mathfrak nL \subseteq \mathfrak a$). -/
theorem isMaximal_normIdeal {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (Q' : QuadraticForm K V)
    {a : Submodule R K} {M : Submodule R V} (hM : OMeara.IsMaximal Q' a M) :
    OMeara.IsMaximal Q' (OMeara.normIdeal Q' M) M :=
  ⟨hM.1, le_rfl, fun N hN hMN hNn => hM.2.2 N hN hMN (hNn.trans hM.2.1)⟩

/-- **Two maximal lattices with the same norm are in the same genus** (O'Meara 1973, proof of Theorem 104:10, p. 321,
with Theorem 91:2): for $Q$ nondegenerate on $F^n$, $n \ge 1$, if $L$ and $K$ are maximal lattices (`IsMaximalLat`)
with $\mathfrak nL = \mathfrak nK$, then $K \in \operatorname{gen}L$. -/
@[kb "omeara1963" "§104, proof of 104:10, p. 321 (maximal lattices of the same norm: gen L = gen K by 91:2)"]
theorem sameGenus_of_isMaximalLat (hQ : Q.Nondegenerate) (hn : 0 < n) {L K : Lat F n} (hL : IsMaximalLat Q L)
    (hK : IsMaximalLat Q K)
    (hnorm : OMeara.normIdeal Q.toQuadraticForm L.1 = OMeara.normIdeal Q.toQuadraticForm K.1) :
    SameGenus Q L.1 K.1 := by
  obtain ⟨a, -, ha⟩ := hL
  obtain ⟨b, -, hb⟩ := hK
  have hfg : (OMeara.normIdeal Q.toQuadraticForm L.1).FG :=
    (OMeara.scale_fg _ L.2.fg).of_le (OMeara.normIdeal_le_scale _ _)
  have hK' := isMaximal_normIdeal _ hb
  rw [← hnorm] at hK'
  exact sameGenus_of_isMaximal Q hQ hfg (normIdeal_ne_bot Q hQ hn L) (isMaximal_normIdeal _ ha) hK'

end QuadFormsKB.Lattices
