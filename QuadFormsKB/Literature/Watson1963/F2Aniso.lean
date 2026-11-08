/-
# An anisotropic plane in a quadratic space over $\mathbb F_2$

A helper for Watson's Lemma 14 at $q = 2$ (the splitting of $\Phi_4 = D_4$ over $\mathbb Z_2$): if $q$ is a quadratic
form on a subspace $W$ of $\mathbb F_2^m$ with polar form $b$ ($q(x + y) = q(x) + q(y) + b(x, y)$), the radical
$\{x \in W : q(x) = 0,\ b(x, W) = 0\}$ is trivial and $\dim W \ge 3$, then there are $x, y \in W$ with
$q(x) = q(y) = b(x, y) = 1$ (`exists_aniso_pair`).

*Proof.* $b \ne 0$ on $W$ (else $q$ is additive and has a nonzero zero). From $e, f$ with $b(e, f) = 1$ either two of
$e, f, e + f$ have $q = 1$, or there is a hyperbolic pair ($q(e) = q(f) = 0$). Then a vector $z'$ of $W$ orthogonal to
$e, f$ and nonzero exists ($\dim W \ge 3$); if $q(z') = 1$ take $e + z', f + z'$; otherwise $z'$ pairs to $1$ with some
$g$ orthogonal to $e, f$ with $q(g) = 0$, and $e + f + z'$, $e + f + g$ work.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Watson1963

variable {m : ℕ}

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem vec_add_self (x : Fin m → ZMod 2) : x + x = 0 := funext fun i => zmod2_add_self (x i)

/-- **An anisotropic plane over $\mathbb F_2$** (see the module docstring). Arguments: the subspace `W`, the
functions `q`, `b`, and the hypotheses: `hb_add` additivity of $b$ in the first argument, `hb_smul` its
homogeneity, `hb_symm` symmetry, `hq` the polar identity on $W$, `hrad` trivial radical, `hdim` $\dim W \ge 3$. -/
theorem exists_aniso_pair (W : Submodule (ZMod 2) (Fin m → ZMod 2)) (q : (Fin m → ZMod 2) → ZMod 2)
    (b : (Fin m → ZMod 2) → (Fin m → ZMod 2) → ZMod 2)
    (hb_add : ∀ x y z, b (x + y) z = b x z + b y z) (hb_smul : ∀ (c : ZMod 2) x y, b (c • x) y = c * b x y)
    (hb_symm : ∀ x y, b x y = b y x)
    (hq : ∀ x ∈ W, ∀ y ∈ W, q (x + y) = q x + q y + b x y)
    (hrad : ∀ x ∈ W, q x = 0 → (∀ y ∈ W, b x y = 0) → x = 0) (hdim : 3 ≤ Module.finrank (ZMod 2) W) :
    ∃ x ∈ W, ∃ y ∈ W, q x = 1 ∧ q y = 1 ∧ b x y = 1 := by
  classical
  have hb_add' : ∀ x y z, b x (y + z) = b x y + b x z := fun x y z => by
    rw [hb_symm, hb_add, hb_symm y, hb_symm z]
  have hb_zero : ∀ y, b 0 y = 0 := fun y => by
    have := hb_add 0 0 y; simp at this; exact this
  have hq0 : q 0 = 0 := by
    have := hq 0 W.zero_mem 0 W.zero_mem; simp [hb_zero] at this; exact this
  have hbxx : ∀ x ∈ W, b x x = 0 := fun x hx => by
    have := hq x hx x hx
    rw [vec_add_self, hq0, zmod2_add_self] at this
    simpa using this.symm
  -- a vector of W outside a subspace of dimension ≤ 2
  have hout : ∀ S : Submodule (ZMod 2) (Fin m → ZMod 2), Module.finrank (ZMod 2) S ≤ 2 → ∃ z ∈ W, z ∉ S := by
    intro S hS
    by_contra h
    push Not at h
    have hle : W ≤ S := fun z hz => h z hz
    have := Submodule.finrank_mono hle
    omega
  have hspan2 : ∀ e f : Fin m → ZMod 2, Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {e, f}) ≤ 2 := by
    intro e f
    have := finrank_span_le_card (R := ZMod 2) ({e, f} : Set (Fin m → ZMod 2))
    refine this.trans ?_
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  -- Step 1: b ≠ 0 on W
  have step1 : ∃ e ∈ W, ∃ f ∈ W, b e f = 1 := by
    by_contra hcon
    push Not at hcon
    have hb0 : ∀ e ∈ W, ∀ f ∈ W, b e f = 0 := fun e he f hf => by
      rcases zmod2_cases (b e f) with h | h
      · exact h
      · exact absurd h (hcon e he f hf)
    have hq1 : ∀ x ∈ W, x ≠ 0 → q x = 1 := fun x hx hne => by
      rcases zmod2_cases (q x) with h | h
      · exact absurd (hrad x hx h (hb0 x hx)) hne
      · exact h
    obtain ⟨x₁, hx₁, hx₁S⟩ := hout ⊥ (by simp)
    have hx₁0 : x₁ ≠ 0 := fun h => hx₁S (by simp [h])
    obtain ⟨x₂, hx₂, hx₂S⟩ := hout (Submodule.span (ZMod 2) {x₁, x₁}) (hspan2 x₁ x₁)
    have hx₂0 : x₂ ≠ 0 := fun h => hx₂S (by simp [h])
    have h12 : x₁ + x₂ ≠ 0 := fun h => by
      apply hx₂S
      have : x₂ = x₁ := by
        have := congrArg (· + x₁) h
        simp only [zero_add] at this
        rw [add_comm x₁ x₂, add_assoc, vec_add_self, add_zero] at this
        exact this
      rw [this]; exact Submodule.subset_span (by simp)
    have := hq x₁ hx₁ x₂ hx₂
    rw [hq1 _ (W.add_mem hx₁ hx₂) h12, hq1 x₁ hx₁ hx₁0, hq1 x₂ hx₂ hx₂0, hb0 x₁ hx₁ x₂ hx₂] at this
    exact absurd this (by decide)
  obtain ⟨e₀, he₀, f₀, hf₀, hb₀⟩ := step1
  -- Step 2: finish, or find a hyperbolic pair
  have hef := hq e₀ he₀ f₀ hf₀
  rw [hb₀] at hef
  have hfin : (∃ x ∈ W, ∃ y ∈ W, q x = 1 ∧ q y = 1 ∧ b x y = 1) ∨
      ∃ e ∈ W, ∃ f ∈ W, q e = 0 ∧ q f = 0 ∧ b e f = 1 := by
    rcases zmod2_cases (q e₀) with h1 | h1 <;> rcases zmod2_cases (q f₀) with h2 | h2
    · exact Or.inr ⟨e₀, he₀, f₀, hf₀, h1, h2, hb₀⟩
    · refine Or.inr ⟨e₀, he₀, e₀ + f₀, W.add_mem he₀ hf₀, h1, ?_, ?_⟩
      · rw [hef, h1, h2]; decide
      · rw [hb_add', hbxx e₀ he₀, hb₀]; simp
    · refine Or.inr ⟨f₀, hf₀, e₀ + f₀, W.add_mem he₀ hf₀, h2, ?_, ?_⟩
      · rw [hef, h1, h2]; decide
      · rw [hb_add', hbxx f₀ hf₀, hb_symm, hb₀]; simp
    · exact Or.inl ⟨e₀, he₀, f₀, hf₀, h1, h2, hb₀⟩
  rcases hfin with h | ⟨e, he, f, hf, hqe, hqf, hbef⟩
  · exact h
  have hbfe : b f e = 1 := by rw [hb_symm]; exact hbef
  -- projection orthogonal to e, f
  set π : (Fin m → ZMod 2) → (Fin m → ZMod 2) := fun z => z + b z f • e + b z e • f with hπ
  have hπW : ∀ z ∈ W, π z ∈ W := fun z hz =>
    W.add_mem (W.add_mem hz (W.smul_mem _ he)) (W.smul_mem _ hf)
  have hπe : ∀ z ∈ W, b (π z) e = 0 := fun z hz => by
    simp only [hπ, hb_add, hb_smul, hbxx e he, hbfe]
    rw [mul_zero, add_zero, mul_one, zmod2_add_self]
  have hπf : ∀ z ∈ W, b (π z) f = 0 := fun z hz => by
    simp only [hπ, hb_add, hb_smul, hbxx f hf, hbef]
    rw [mul_zero, add_zero, mul_one, zmod2_add_self]
  have hπq : ∀ z ∈ W, ∀ y, b y e = 0 → b y f = 0 → b (π z) y = b z y := fun z hz y hye hyf => by
    simp only [hπ, hb_add, hb_smul, hb_symm e y, hb_symm f y, hye, hyf]; simp
  obtain ⟨z, hz, hzS⟩ := hout (Submodule.span (ZMod 2) {e, f}) (hspan2 e f)
  obtain ⟨z', hz'W, hz', hz'e, hz'f⟩ : ∃ z', z' ∈ W ∧ z' ≠ 0 ∧ b z' e = 0 ∧ b z' f = 0 := by
    refine ⟨π z, hπW z hz, fun h0 => ?_, hπe z hz, hπf z hz⟩
    apply hzS
    set w := b z f • e + b z e • f
    have h0' : z + w = 0 := by rw [← add_assoc]; exact h0
    have : z = w := by
      calc z = (z + w) + w := by rw [add_assoc, vec_add_self, add_zero]
        _ = w := by rw [h0', zero_add]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hez' : b e z' = 0 := by rw [hb_symm]; exact hz'e
  have hfz' : b f z' = 0 := by rw [hb_symm]; exact hz'f
  rcases zmod2_cases (q z') with hqz | hqz
  · -- q(z') = 0: z' pairs to 1 with some g ⊥ e, f with q(g) = 0
    have hex : ∃ w ∈ W, b z' w = 1 := by
      by_contra hcon
      push Not at hcon
      exact hz' (hrad z' hz'W hqz fun w hw => (zmod2_cases _).resolve_right (hcon w hw))
    obtain ⟨w, hw, hbw⟩ := hex
    have hw'W := hπW w hw
    have hw'e := hπe w hw
    have hw'f := hπf w hw
    have hbzw' : b z' (π w) = 1 := by rw [hb_symm, hπq w hw z' hz'e hz'f, hb_symm]; exact hbw
    obtain ⟨g, hgW, hge, hgf, hqg, hbzg⟩ : ∃ g ∈ W, b g e = 0 ∧ b g f = 0 ∧ q g = 0 ∧ b z' g = 1 := by
      rcases zmod2_cases (q (π w)) with h0 | h1
      · exact ⟨π w, hw'W, hw'e, hw'f, h0, hbzw'⟩
      · refine ⟨π w + z', W.add_mem hw'W hz'W, by rw [hb_add, hw'e, hz'e]; simp,
          by rw [hb_add, hw'f, hz'f]; simp, ?_, ?_⟩
        · rw [hq _ hw'W _ hz'W, h1, hqz, hb_symm, hbzw']; decide
        · rw [hb_add', hbzw', hbxx z' hz'W]; simp
    have hEF : e + f ∈ W := W.add_mem he hf
    have hqEF : q (e + f) = 1 := by rw [hq e he f hf, hqe, hqf, hbef]; simp
    have hbEFz : b (e + f) z' = 0 := by rw [hb_add, hez', hfz']; simp
    have hbEFg : b (e + f) g = 0 := by rw [hb_add, hb_symm e, hb_symm f, hge, hgf]; simp
    refine ⟨e + f + z', W.add_mem hEF hz'W, e + f + g, W.add_mem hEF hgW, ?_, ?_, ?_⟩
    · rw [hq _ hEF _ hz'W, hqEF, hqz, hbEFz]; simp
    · rw [hq _ hEF _ hgW, hqEF, hqg, hbEFg]; simp
    · have heg : b e g = 0 := by rw [hb_symm]; exact hge
      have hfg : b f g = 0 := by rw [hb_symm]; exact hgf
      simp only [hb_add, hb_add', hbxx e he, hbxx f hf, hbef, hbfe, heg, hfg, hz'e, hz'f, hbzg]
      decide
  · refine ⟨e + z', W.add_mem he hz'W, f + z', W.add_mem hf hz'W, ?_, ?_, ?_⟩
    · rw [hq e he z' hz'W, hqe, hqz, hez']; simp
    · rw [hq f hf z' hz'W, hqf, hqz, hfz']; simp
    · simp only [hb_add, hb_add', hbef, hez', hz'f, hbxx z' hz'W]
      decide

end QuadFormsKB.Watson1963
