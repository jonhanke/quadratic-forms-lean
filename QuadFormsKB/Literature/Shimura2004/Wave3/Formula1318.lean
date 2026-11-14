/-
# Shimura 2004, (13.18): the mass of $H$ from the solution sets, conditional on Theorem 11.6 (ii)

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 11.6 (i), (ii)
(printed p. 104), Theorem 13.12 (13.17b) and formula (13.18) (pp. 134–135). Page numbers are printed pages.

**Setting.** As in `HGenus.lean`: $F$ a number field, $V = F^n$ with `Q : QuadForm F n`, $L$ a
$\mathfrak g$-maximal lattice, $h \in V$ with $q = \varphi[h] \ne 0$, $\mathfrak b = \varphi(h, L)$,
$H = SO^\varphi(W)$, $W = (Fh)^\perp$, embedded in $G = SO^\varphi(V)$ (`hRat Q h`), $H_{\mathbf h}$ (`hAf Q h`),
$C$ the stabilizer of $L$ (`stabC Q L`), and $\{L_i\}_{i \in I}$ a minimal family in the $H$-genus of $L$ whose
$G$-classes cover it (`IsHGenusCover`). Write $D = H_{\mathbf h} \cap C$. The group $H$ acts on $H_{\mathbf h}/D$ by
left multiplication, with orbits $H\backslash H_{\mathbf h}/D$ and stabilizers $H \cap \xi D\xi^{-1}
= H \cap \xi C\xi^{-1}$; $\Gamma(L_i)$ acts on $L_i[q,\mathfrak b]$ (`gammaLat_mulAction`).

**Theorem 11.6 (i), (ii)** (stated here as `Theorem11_6_ii`): Shimura's correspondence $k = h\alpha \mapsto H\xi D$
is a bijection $\bigsqcup_i L_i[q,\mathfrak b]/\Gamma(L_i) \to H\backslash H_{\mathbb A}/D$ ((i)), and the stabilizer
of $k$ in $\Gamma(L_i)$ is conjugate to $H \cap \xi C\xi^{-1}$ ((ii)). The statement here keeps exactly what (13.18)
needs: the existence of maps $g_i : L_i[q,\mathfrak b] \to H_{\mathbf h}/D$ inducing that bijection of orbit sets and
preserving the orders of stabilizers. (Shimura's (ii), an isomorphism of stabilizers, implies the equality of orders.)

**Proves** (conditional on the named input `FundamentalTheorem11_6_ii`; standard axioms only):
* `formula_13_18`: the stated proposition `Formula13_18` (`HGenus.lean`), i.e. (13.18)
  $\sum_i [\Gamma(L_i):1]^{-1}\#L_i[q,\mathfrak b] = m(H, H_{\mathbb A} \cap C)$ in the totally positive definite
  case. The proof: $\#L_i[q,\mathfrak b]/\#\Gamma(L_i)$ is the mass of the action of $\Gamma(L_i)$ (class formula,
  `Tamagawa.orbitMass_of_finite`, with the finiteness `finite_gammaLat`, `finite_solSetLat`), and the
  correspondence of Theorem 11.6 identifies the sum of these masses with the double coset mass
  `Tamagawa.dcMass`.
-/
import QuadFormsKB.Literature.Shimura2004.Wave3.MassSolutions
import QuadFormsKB.Citation

open NumberField Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

/-- The subgroup $H$ (diagonally embedded) of $H_{\mathbf h}$. -/
abbrev hInAf {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (h : Fin n → F) :
    Subgroup (hAf Q h) :=
  ((hRat Q h).map (diagF Q)).subgroupOf (hAf Q h)

/-- The subgroup $D = H_{\mathbf h} \cap C$ of $H_{\mathbf h}$. -/
abbrev hStabAf {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (h : Fin n → F) (L : Lat F n) :
    Subgroup (hAf Q h) :=
  (stabC Q L).subgroupOf (hAf Q h)

/-- **Theorem 11.6 (i), (ii)** (Shimura 2004, p. 104), in the form used for (13.18): with the assumptions of
Theorem 11.6 (`Theorem11_6_i`), the index set $I$ is finite and there are maps
$g_i : L_i[q,\mathfrak b] \to H_{\mathbf h}/D$ ($D = H_{\mathbf h} \cap C$) such that
* `orbit`: $x, y \in L_i[q,\mathfrak b]$ are in one $\Gamma(L_i)$-orbit iff $g_i(x), g_i(y)$ are in one $H$-orbit;
* `disjoint`: if $g_i(x)$ and $g_j(y)$ are in one $H$-orbit then $i = j$;
* `onto`: every $H$-orbit of $H_{\mathbf h}/D$ contains some $g_i(x)$;
* `stab`: the stabilizer of $x$ in $\Gamma(L_i)$ and the stabilizer $H \cap \xi D\xi^{-1}$ of $g_i(x) = \xi D$ in $H$
  have the same order.
The first three say that $(i, x) \mapsto H g_i(x)$ is Shimura's bijection
$\bigsqcup_i L_i[q,\mathfrak b]/\Gamma(L_i) \cong H\backslash H_{\mathbf h}/D$ of (i); the last is (ii).
*Stated, not proved* (the proof uses Theorem 10.5 at every prime). -/
@[kb "shimura2004" "Thm. 11.6 (i), (ii), p. 104 (orbit correspondence with stabilizers H ∩ ξCξ⁻¹)"]
def Theorem11_6_ii : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate →
    2 < n → Cond92 Q → ∀ L : Lat F n, IsGMaximal Q L → ∀ h : Fin n → F, Q.eval h ≠ 0 →
    letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
    let b := phiIdeal Q.toQuadraticForm h L.1
    ∀ (I : Type) (Ls : I → Lat F n), IsHGenusCover Q h L Ls →
      Finite I ∧ ∃ g : ∀ i, solSetLat Q (Ls i) (Q.eval h) b → hAf Q h ⧸ hStabAf Q h L,
        (∀ i x y, y ∈ orbit (gammaLat Q (Ls i)) x ↔ g i y ∈ orbit (hInAf Q h) (g i x)) ∧
        (∀ i j x y, g j y ∈ orbit (hInAf Q h) (g i x) → i = j) ∧
        (∀ z : hAf Q h ⧸ hStabAf Q h L, ∃ i x, g i x ∈ orbit (hInAf Q h) z) ∧
        (∀ i x, Nat.card (stabilizer (gammaLat Q (Ls i)) x) = Nat.card (stabilizer (hInAf Q h) (g i x)))

/-- **Cited input: Theorem 11.6 (i), (ii)** (`Theorem11_6_ii`), as a named structure so that its use as a hypothesis
is explicit. Stated, not proved here. -/
@[kb "shimura2004" "Thm. 11.6 (i), (ii), p. 104 (as an input)"]
structure FundamentalTheorem11_6_ii : Prop where
  holds : Theorem11_6_ii

/-- Sum of masses over a family of actions in bijection with the orbits of one action. -/
theorem sum_orbitMass_eq_orbitMass {I : Type} [Finite I] {Γ : I → Type} [∀ i, Group (Γ i)] {X : I → Type}
    [∀ i, MulAction (Γ i) (X i)] [∀ i, Finite (X i)] {H Y : Type} [Group H] [MulAction H Y]
    (g : ∀ i, X i → Y) (horb : ∀ i x y, y ∈ orbit (Γ i) x ↔ g i y ∈ orbit H (g i x))
    (hdisj : ∀ i j x y, g j y ∈ orbit H (g i x) → i = j)
    (honto : ∀ z : Y, ∃ i x, g i x ∈ orbit H z)
    (hstab : ∀ i x, Nat.card (stabilizer (Γ i) x) = Nat.card (stabilizer H (g i x))) :
    ∑ᶠ i, orbitMass (Γ i) (X i) = orbitMass H Y := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hfinO : ∀ i, Finite (orbitRel.Quotient (Γ i) (X i)) := fun i =>
    Finite.of_surjective (fun x : X i => (Quotient.mk'' x : orbitRel.Quotient (Γ i) (X i)))
      (fun ω => ⟨ω.out, Quotient.out_eq' ω⟩)
  have : ∀ i, Fintype (orbitRel.Quotient (Γ i) (X i)) := fun i => Fintype.ofFinite _
  -- the map on orbit sets
  let Φ : (Σ i, orbitRel.Quotient (Γ i) (X i)) → orbitRel.Quotient H Y :=
    fun p => Quotient.mk'' (g p.1 p.2.out)
  have hmem : ∀ (i : I) (x : X i), (Quotient.mk'' x : orbitRel.Quotient (Γ i) (X i)).out ∈ orbit (Γ i) x := by
    intro i x
    have := Quotient.out_eq' (Quotient.mk'' x : orbitRel.Quotient (Γ i) (X i))
    have h2 := Quotient.exact' this
    rw [orbitRel_apply] at h2
    exact h2
  have hΦbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨i, ω⟩ ⟨j, ω'⟩ hp
      have h1 := Quotient.exact' hp
      rw [orbitRel_apply] at h1
      obtain rfl := hdisj j i ω'.out ω.out h1
      have h3 := (horb _ ω'.out ω.out).2 h1
      have : ω = ω' := by
        rw [← Quotient.out_eq' ω, ← Quotient.out_eq' ω']
        exact Quotient.sound' (by rw [orbitRel_apply]; exact h3)
      rw [this]
    · intro z
      induction z using Quotient.inductionOn' with | h y => ?_
      obtain ⟨i, x, hx⟩ := honto y
      refine ⟨⟨i, Quotient.mk'' x⟩, ?_⟩
      apply Quotient.sound'
      rw [orbitRel_apply]
      -- `g i (out ⟦x⟧) ∈ orbit (g i x)` and `g i x ∈ orbit y`
      have h1 : g i (Quotient.mk'' x : orbitRel.Quotient (Γ i) (X i)).out ∈ orbit H (g i x) :=
        (horb i x _).1 (hmem i x)
      rw [orbit_eq_iff.2 hx] at h1
      exact h1
  unfold orbitMass
  rw [← finsum_comp_equiv (Equiv.ofBijective Φ hΦbij)]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Equiv.ofBijective_apply]
  have h1 : (Φ ⟨i, ω⟩).out ∈ orbit H (g i ω.out) := by
    apply out_mem_orbit
    rfl
  rw [card_stabilizer_of_mem_orbit h1, ← hstab]

/-- **(13.18)** (Shimura 2004, p. 134; Theorem 13.12 (13.17b) in the totally definite case), *conditional on the
named input* `FundamentalTheorem11_6_ii` (Theorem 11.6 (i), (ii)): the proposition `Formula13_18`,
$$\sum_{i\in I}[\Gamma(L_i):1]^{-1}\,\#L_i[q,\mathfrak b] = m(H, H_{\mathbb A}\cap C).$$ -/
@[kb "shimura2004" "(13.18), p. 134 (from Theorem 11.6 (i), (ii))"]
theorem formula_13_18 (hin : FundamentalTheorem11_6_ii) : Formula13_18 := by
  intro F _ _ n Q hQ hpd hn h92 L hL h hh b I Ls hcov
  obtain ⟨hI, g, horb, hdisj, honto, hstab⟩ := hin.holds F n Q hQ hn h92 L hL h hh I Ls hcov
  have hfinX : ∀ i, Finite (solSetLat Q (Ls i) (Q.eval h) b) := fun i =>
    (finite_solSetLat hpd (Ls i) (Q.eval h) b).to_subtype
  have hfinG : ∀ i, Finite (gammaLat Q (Ls i)) := fun i => finite_gammaLat hpd (Ls i)
  have hterm : ∀ i, ((solSetLat Q (Ls i) (Q.eval h) b).ncard : ℝ) / Nat.card (gammaLat Q (Ls i)) =
      orbitMass (gammaLat Q (Ls i)) (solSetLat Q (Ls i) (Q.eval h) b) := by
    intro i
    rw [orbitMass_of_finite, Nat.card_coe_set_eq]
  simp_rw [hterm]
  exact sum_orbitMass_eq_orbitMass g horb hdisj honto hstab

end QuadFormsKB.Shimura2004
