/-
# Kneser neighbours, worked example 1: the 3-neighbours of $I_4 = x_0^2 + x_1^2 + x_2^2 + x_3^2$

**Certified computation.** The generator (`Siegel/KneserGen.lean`) lists the $16 = (3+1)^2$ isotropic lines of
$x_0^2 + \dots + x_3^2$ over $\mathbb{F}_3$, builds each $3$-neighbour $L(\vec{v})$ of $\mathbb{Z}^4$, reduces its Gram form and finds a basis in
which the Gram form is again $I_4$. The output `certsI4` (16 neighbour certificates, pasted below) is checked by the kernel:
- `certsI4_valid` (`decide`): each certificate is valid for $(I_4, 3, I_4)$;
- `certsI4_cover` (`decide`): the certificates cover every isotropic line of $\mathbb{F}_3^4$.

**Results.**
- `isNbrForm_sumSq_four` / `nbrClosed_sumSq_four`: **every $3$-neighbour of $(\mathbb{Z}^4, I_4)$ is isometric to $I_4$**; the class of
  $I_4$ is closed under $3$-neighbour steps (unconditional).
- `genus_sumSq_four_of_kneser`: with `KneserConnected 3 I₄` (Kneser's theorem; conditional) the closure criterion gives
  $\mathrm{Gen}(I_4) = \{[I_4]\}$.
- `genusClasses_sumSq_four_mass`: the **mass check** $1/|\mathrm{Aut}(I_4)| = 1/384 = \mathrm{Mass}(I_4)$ and the mass criterion
  `genusClasses_eq_of_sum_eq_mass`. Here the value of the mass comes from the proved class-number-one theorem
  (`genusClasses_sumSq`), so this instance only illustrates the criterion; both routes agree with it.

## Worked example 2: the genus of $Q_1 = x_0^2 + x_1^2 + 7x_2^2$ (class number 2), $p = 3$

- `sameGenus_Q₁_Q₂`: $Q_2 = x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$ is a $3$-neighbour form of $Q_1$, hence in its genus
  (certificate; unconditional).
- `card_aut_Q₁`, `card_aut_Q₂`: $|\mathrm{Aut}(Q_1)| = 16$, $|\mathrm{Aut}(Q_2)| = 8$ (certified enumeration, `card_aut_eq_of_cert`);
  so `not_intEquiv_Q₁_Q₂`: $Q_1 \not\sim Q_2$, and `mass_Q₁_ge`: $\mathrm{Mass}(Q_1) \ge 1/16 + 1/8 = 3/16$ (unconditional).
- `nbrClosed_Q₁Q₂`: every $3$-neighbour form of $Q_1$ or $Q_2$ is equivalent to $Q_1$ or $Q_2$ (all $4 + 4$ isotropic lines
  certified; unconditional).
- `genusClasses_Q₁_of_kneser`: with `KneserConnected 3 Q₁` (Kneser's theorem), $\mathrm{Gen}(Q_1) = \{[Q_1], [Q_2]\}$ and
  $\mathrm{Mass}(Q_1) = 3/16$; this agrees with the Smith–Minkowski–Siegel mass $3/16$ (Magma `Mass`, cross-check, not
  formalized).
-/
import QuadFormsKB.Siegel.KneserAut

open Matrix

namespace QuadFormsKB.Siegel.Kneser.Examples

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

/-- **The 16 certified $3$-neighbours of $I_4$**, each with a basis in which its Gram form is $I_4$ (generator output). -/
def certsI4 : List (NbCert 4 × QuadForm ℤ 4) :=
  [(⟨![4, 1, 1, 0], !![1, 2, 2, 0; -2, -1, 2, 0; -2, 2, -1, 0; 0, 0, 0, -3], ![1, 2, 2, 0], ![2, 0, 0, 0], !![-5, -2, -2, 0; -10, -3, -2, 0; -10, -2, -3, 0; 0, 0, 0, -1], ![2, 4, 4, 0], ![0, 1, 1, 0], !![1, -2, -2, 0; 2, -1, 2, 0; 2, 2, -1, 0; 0, 0, 0, -3]⟩, sumSq 4),
  (⟨![7, 2, 1, 0], !![-2, -1, -2, 0; -1, -2, 2, 0; -2, 2, 1, 0; 0, 0, 0, -3], ![1, 2, 1, 0], ![2, 0, 0, 0], !![18, 5, 2, 0; 9, 2, 2, 0; 18, 6, 3, 0; 0, 0, 0, -1], ![-4, -2, -4, 0], ![-2, -1, -1, 0], !![-2, -1, -2, 0; -1, -2, 2, 0; -2, 2, 1, 0; 0, 0, 0, -3]⟩, sumSq 4),
  (⟨![7, 1, 2, 0], !![2, -1, 2, 0; 2, 2, -1, 0; 1, -2, -2, 0; 0, 0, 0, -3], ![2, 2, 2, 0], ![2, 0, 0, 0], !![-18, -2, -5, 0; 9, 2, 2, 0; -18, -3, -6, 0; 0, 0, 0, -1], ![4, -2, 4, 0], ![2, -1, 1, 0], !![2, 2, 1, 0; -1, 2, -2, 0; 2, -1, -2, 0; 0, 0, 0, -3]⟩, sumSq 4),
  (⟨![1, 2, 2, 0], !![0, 2, 2, -1; 0, 1, -2, -2; 0, -2, 1, -2; -3, 0, 0, 0], ![0, 2, 2, 2], ![2, 0, 0, 0], !![0, 0, 0, -1; -2, -5, -6, 0; -2, -6, -5, 0; 1, 2, 2, 0], ![0, 4, 4, -2], ![0, 0, 0, -1], !![0, 0, 0, -3; 2, 1, -2, 0; 2, -2, 1, 0; -1, -2, -2, 0]⟩, sumSq 4),
  (⟨![4, 1, 0, 1], !![1, 2, 2, 0; -2, -1, 2, 0; 0, 0, 0, -3; -2, 2, -1, 0], ![1, 2, 2, 0], ![2, 0, 0, 0], !![-5, -2, 0, -2; -10, -3, 0, -2; -10, -2, 0, -3; 0, 0, -1, 0], ![2, 4, 4, 0], ![0, 1, 1, 0], !![1, -2, 0, -2; 2, -1, 0, 2; 2, 2, 0, -1; 0, 0, -3, 0]⟩, sumSq 4),
  (⟨![7, 2, 0, 1], !![-2, -1, -2, 0; -1, -2, 2, 0; 0, 0, 0, -3; -2, 2, 1, 0], ![1, 2, 1, 0], ![2, 0, 0, 0], !![18, 5, 0, 2; 9, 2, 0, 2; 18, 6, 0, 3; 0, 0, -1, 0], ![-4, -2, -4, 0], ![-2, -1, -1, 0], !![-2, -1, 0, -2; -1, -2, 0, 2; -2, 2, 0, 1; 0, 0, -3, 0]⟩, sumSq 4),
  (⟨![4, 0, 1, 1], !![1, 2, 2, 0; 0, 0, 0, -3; -2, -1, 2, 0; -2, 2, -1, 0], ![1, 2, 2, 0], ![2, 0, 0, 0], !![-5, 0, -2, -2; -10, 0, -3, -2; -10, 0, -2, -3; 0, -1, 0, 0], ![2, 4, 4, 0], ![0, 1, 1, 0], !![1, 0, -2, -2; 2, 0, -1, 2; 2, 0, 2, -1; 0, -3, 0, 0]⟩, sumSq 4),
  (⟨![0, 4, 1, 1], !![0, 0, 0, -3; 1, 2, 2, 0; -2, -1, 2, 0; -2, 2, -1, 0], ![1, 2, 2, 0], ![0, 2, 0, 0], !![0, -5, -2, -2; 0, -10, -3, -2; 0, -10, -2, -3; -1, 0, 0, 0], ![2, 4, 4, 0], ![0, 1, 1, 0], !![0, 1, -2, -2; 0, 2, -1, 2; 0, 2, 2, -1; -3, 0, 0, 0]⟩, sumSq 4),
  (⟨![7, 0, 2, 1], !![-2, -1, -2, 0; 0, 0, 0, -3; -1, -2, 2, 0; -2, 2, 1, 0], ![1, 2, 1, 0], ![2, 0, 0, 0], !![18, 0, 5, 2; 9, 0, 2, 2; 18, 0, 6, 3; 0, -1, 0, 0], ![-4, -2, -4, 0], ![-2, -1, -1, 0], !![-2, 0, -1, -2; -1, 0, -2, 2; -2, 0, 2, 1; 0, -3, 0, 0]⟩, sumSq 4),
  (⟨![0, 7, 2, 1], !![0, 0, 0, -3; -2, -1, -2, 0; -1, -2, 2, 0; -2, 2, 1, 0], ![1, 2, 1, 0], ![0, 2, 0, 0], !![0, 18, 5, 2; 0, 9, 2, 2; 0, 18, 6, 3; -1, 0, 0, 0], ![-4, -2, -4, 0], ![-2, -1, -1, 0], !![0, -2, -1, -2; 0, -1, -2, 2; 0, -2, 2, 1; -3, 0, 0, 0]⟩, sumSq 4),
  (⟨![7, 1, 0, 2], !![2, -1, 2, 0; 2, 2, -1, 0; 0, 0, 0, -3; 1, -2, -2, 0], ![2, 2, 2, 0], ![2, 0, 0, 0], !![-18, -2, 0, -5; 9, 2, 0, 2; -18, -3, 0, -6; 0, 0, -1, 0], ![4, -2, 4, 0], ![2, -1, 1, 0], !![2, 2, 0, 1; -1, 2, 0, -2; 2, -1, 0, -2; 0, 0, -3, 0]⟩, sumSq 4),
  (⟨![1, 2, 0, 2], !![2, 0, 2, -1; 1, 0, -2, -2; 0, -3, 0, 0; -2, 0, 1, -2], ![2, 0, 2, 2], ![2, 0, 0, 0], !![-2, -5, 0, -6; 0, 0, -1, 0; -2, -6, 0, -5; 1, 2, 0, 2], ![4, 0, 4, -2], ![0, 0, 0, -1], !![2, 1, 0, -2; 0, 0, -3, 0; 2, -2, 0, 1; -1, -2, 0, -2]⟩, sumSq 4),
  (⟨![7, 0, 1, 2], !![2, -1, 2, 0; 0, 0, 0, -3; 2, 2, -1, 0; 1, -2, -2, 0], ![2, 2, 2, 0], ![2, 0, 0, 0], !![-18, 0, -2, -5; 9, 0, 2, 2; -18, 0, -3, -6; 0, -1, 0, 0], ![4, -2, 4, 0], ![2, -1, 1, 0], !![2, 0, 2, 1; -1, 0, 2, -2; 2, 0, -1, -2; 0, -3, 0, 0]⟩, sumSq 4),
  (⟨![0, 7, 1, 2], !![0, 0, 0, -3; 2, -1, 2, 0; 2, 2, -1, 0; 1, -2, -2, 0], ![2, 2, 2, 0], ![0, 2, 0, 0], !![0, -18, -2, -5; 0, 9, 2, 2; 0, -18, -3, -6; -1, 0, 0, 0], ![4, -2, 4, 0], ![2, -1, 1, 0], !![0, 2, 2, 1; 0, -1, 2, -2; 0, 2, -1, -2; -3, 0, 0, 0]⟩, sumSq 4),
  (⟨![1, 0, 2, 2], !![2, 2, 0, -1; 0, 0, -3, 0; 1, -2, 0, -2; -2, 1, 0, -2], ![2, 2, 0, 2], ![2, 0, 0, 0], !![-2, 0, -5, -6; -2, 0, -6, -5; 0, -1, 0, 0; 1, 0, 2, 2], ![4, 4, 0, -2], ![0, 0, 0, -1], !![2, 0, 1, -2; 2, 0, -2, 1; 0, -3, 0, 0; -1, 0, -2, -2]⟩, sumSq 4),
  (⟨![0, 1, 2, 2], !![0, 0, 0, -3; 2, 2, -1, 0; 1, -2, -2, 0; -2, 1, -2, 0], ![2, 2, 2, 0], ![0, 2, 0, 0], !![0, -2, -5, -6; 0, -2, -6, -5; 0, 1, 2, 2; -1, 0, 0, 0], ![4, 4, -2, 0], ![0, 0, -1, 0], !![0, 2, 1, -2; 0, 2, -2, 1; 0, -1, -2, -2; -3, 0, 0, 0]⟩, sumSq 4)]

/-- Every certificate in `certsI4` is valid (kernel check). -/
theorem certsI4_valid : ∀ c ∈ certsI4, c.1.Valid (sumSq 4) c.2 3 := by decide

/-- The certificates cover all isotropic lines of $\mathbb{F}_3^4$ (kernel check over the $81$ vectors of $\{0, 1, 2\}^4$). -/
theorem certsI4_cover : ∀ u ∈ Gen.allVecs 3 4, (∃ i, ¬ ((3 : ℕ) : ℤ) ∣ u i) → ((3 : ℕ) : ℤ) ∣ (sumSq 4).eval u →
    ∃ c ∈ certsI4, ∃ a < (3 : ℕ), ∀ i, ((3 : ℕ) : ℤ) ∣ u i - (a : ℤ) * c.1.v i := by decide

/-- $3 \nmid \det H_{I_4} = 16$ (certificate $H \cdot 1 = 2 \cdot 1$). -/
theorem not_three_dvd_det : ¬ ((3 : ℕ) : ℤ) ∣ (sumSq 4).hessian.det :=
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  DetCert.not_dvd_det (c := ⟨1, 2⟩) (by decide)

/-- **Every $3$-neighbour of $(\mathbb{Z}^4, x_0^2 + x_1^2 + x_2^2 + x_3^2)$ is isometric to $I_4$:** every $3$-neighbour form is
$\mathrm{GL}_4(\mathbb{Z})$-equivalent to $I_4$. Certified computation (`certsI4_valid`, `certsI4_cover`). -/
@[kb "kneser1957" "§2, neighbour enumeration [unverified]"]
theorem isNbrForm_sumSq_four {Q' : QuadForm ℤ 4} (h : IsNbrForm 3 (sumSq 4) Q') : IntEquiv (sumSq 4) Q' := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c, hc, he⟩ := exists_intEquiv_of_cover not_three_dvd_det certsI4 certsI4_valid certsI4_cover h
  have hc2 : c.2 = sumSq 4 := by
    simp only [certsI4, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
  rwa [hc2] at he

/-- **The class of $I_4$ is closed under $3$-neighbour steps** (the hypothesis of the closure criterion for $S = [I_4]$). -/
theorem nbrClosed_sumSq_four :
    ∀ s ∈ [sumSq 4], ∀ Q', IsNbrForm 3 s Q' → ∃ s' ∈ [sumSq 4], IntEquiv s' Q' := by
  intro s hs Q' h
  rw [List.mem_singleton] at hs; subst hs
  exact ⟨sumSq 4, List.mem_singleton_self _, isNbrForm_sumSq_four h⟩

/-- **The genus of $I_4$ via the closure criterion** (conditional on `KneserConnected 3 I₄`, i.e. Kneser's theorem for
this genus): every form in the genus of $I_4$ is equivalent to $I_4$. (Agrees with the proved `genusClasses_sumSq`.) -/
@[kb "kneser1957" "§2 [unverified]"]
theorem genus_sumSq_four_of_kneser (hK : KneserConnected 3 (sumSq 4)) {Q' : QuadForm ℤ 4}
    (h : SameGenus (sumSq 4) Q') : IntEquiv (sumSq 4) Q' := by
  obtain ⟨s, hs, he⟩ := exists_intEquiv_of_closed hK [sumSq 4] ⟨sumSq 4, List.mem_singleton_self _,
    IsometricGL.refl _⟩ nbrClosed_sumSq_four h
  rw [List.mem_singleton] at hs; subst hs; exact he

/-- **The mass check for $I_4$:** $1/|\mathrm{Aut}(I_4)| = 1/384 = \mathrm{Mass}(I_4)$, and the mass criterion
(`genusClasses_eq_of_sum_eq_mass`) gives $\mathrm{Gen}(I_4) = \{[I_4]\}$. -/
@[kb "conwaysloane1988" "mass check for I_4"]
theorem genusClasses_sumSq_four_mass :
    ((Nat.card (Aut (sumSq 4)) : ℝ))⁻¹ = 1 / 384 ∧ mass (sumSq 4) = 1 / 384 ∧
      genusClasses (sumSq 4) = Set.range fun _ : Fin 1 => classOf (sumSq 4) := by
  have hA : Nat.card (Aut (sumSq 4)) = 384 := by rw [card_aut_sumSq]; decide
  have hm : mass (sumSq 4) = 1 / 384 := by
    rw [mass, genusClasses_sumSq (by norm_num), finsum_mem_singleton, QClass.autCard_classOf, hA]; norm_num
  refine ⟨by rw [hA]; norm_num, hm, ?_⟩
  refine genusClasses_eq_of_sum_eq_mass posDef_sumSq (fun _ : Fin 1 => sumSq 4) (fun _ => SameGenus.refl _)
    (fun i j _ => Subsingleton.elim i j) ?_
  rw [hm, Fin.sum_univ_one, hA]; norm_num

/-! ### Worked example 2: $x_0^2 + x_1^2 + 7x_2^2$ -/

/-- $Q_1 = x_0^2 + x_1^2 + 7x_2^2$. -/
def Q₁ : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 1, 0], ![0, 0, 7]]
/-- $Q_2 = x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$. -/
def Q₂ : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 2, -2], ![0, 0, 4]]

theorem eval_Q₁ (x : Fin 3 → ℤ) : Q₁.eval x = x 0 ^ 2 + x 1 ^ 2 + 7 * x 2 ^ 2 := by
  simp [Q₁, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]; ring

theorem eval_Q₂ (x : Fin 3 → ℤ) : Q₂.eval x = x 0 ^ 2 + 2 * x 1 ^ 2 - 2 * x 1 * x 2 + 4 * x 2 ^ 2 := by
  simp [Q₂, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]; ring

theorem ne_zero_cases {x : Fin 3 → ℤ} (hx : x ≠ 0) : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2])

theorem posDef_Q₁ : IntQF.PosDef Q₁ := by
  intro x hx
  rw [eval_Q₁]
  rcases ne_zero_cases hx with h | h | h <;> positivity

theorem posDef_Q₂ : IntQF.PosDef Q₂ := by
  intro x hx
  rw [eval_Q₂]
  have e : x 0 ^ 2 + 2 * x 1 ^ 2 - 2 * x 1 * x 2 + 4 * x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 + (x 1 - x 2) ^ 2 + 3 * x 2 ^ 2 := by
    ring
  rw [e]
  rcases ne_zero_cases hx with h | h | h <;> positivity

theorem not_three_dvd_det_Q₁ : ¬ ((3 : ℕ) : ℤ) ∣ Q₁.hessian.det :=
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  DetCert.not_dvd_det (c := ⟨!![28, 0, 0; 0, 28, 0; 0, 0, 4], 56⟩) (by decide)

theorem not_three_dvd_det_Q₂ : ¬ ((3 : ℕ) : ℤ) ∣ Q₂.hessian.det :=
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  DetCert.not_dvd_det (c := ⟨!![28, 0, 0; 0, 16, 4; 0, 4, 8], 56⟩) (by decide)

/-- **The certified $3$-neighbours of $Q_1$** (generator output; all four are equivalent to $Q_2$). -/
def certsQ₁ : List (NbCert 3 × QuadForm ℤ 3) :=
  [(⟨![1, 1, 1], !![-1, -3, 5; -1, 3, 2; -1, 0, -1], ![2, 0, 2], ![2, 0, 0], !![1, 1, 7; 1, 2, 9; -1, -1, -10], ![-2, -2, 2], ![-1, 0, 0], !![-1, -1, -7; -1, 2, -1; 1, 1, -2]⟩, Q₂),
  (⟨![4, 2, 1], !![-1, 3, -5; 1, 3, 2; -1, 0, 1], ![2, 0, 1], ![2, 0, 0], !![5, 3, 7; -5, -2, -9; 5, 3, 10], ![-2, 2, -2], ![-1, 1, 0], !![-1, 1, -7; 1, 2, 1; -1, 1, 2]⟩, Q₂),
  (⟨![4, 1, 2], !![-1, -3, 5; -1, 3, 2; 1, 0, 1], ![2, 0, 2], ![2, 0, 0], !![5, 1, 21; 5, 2, 19; -5, -1, -18], ![-2, -2, 2], ![1, 0, 1], !![-1, -1, 7; -1, 2, 1; 1, 1, 2]⟩, Q₂),
  (⟨![7, 2, 2], !![-1, -3, 5; 1, -3, -2; 1, 0, 1], ![2, 0, 2], ![2, 0, 0], !![9, 3, 21; 9, 2, 19; -9, -3, -18], ![-2, -2, 2], ![1, -1, 1], !![-1, 1, 7; -1, -2, 1; 1, -1, 2]⟩, Q₂)]

/-- **The certified $3$-neighbours of $Q_2$** (generator output). -/
def certsQ₂ : List (NbCert 3 × QuadForm ℤ 3) :=
  [(⟨![4, 1, 0], !![-1, -4, 2; 2, -1, 2; 0, 0, 3], ![2, 2, 2], ![2, 0, 0], !![5, 4, -2; 10, 5, -2; 0, 0, 1], ![-2, -4, 0], ![0, -1, 0], !![-1, 4, -2; -2, -1, 2; 0, 0, 3]⟩, Q₂),
  (⟨![1, 2, 0], !![-1, 4, -2; -2, -1, 2; 0, 0, 3], ![2, 1, 1], ![2, 0, 0], !![1, 4, -2; -2, -11, 6; 0, 0, 1], ![-2, 4, 0], ![-1, 0, 0], !![-1, -4, 2; 2, -1, 2; 0, 0, 3]⟩, Q₂),
  (⟨![1, 2, 1], !![1, -1, 7; -1, -2, -1; 1, -1, -2], ![1, 2, 1], ![2, 0, 0], !![-1, -5, -1; 1, 3, 2; -1, -4, -3], ![2, -2, 2], ![0, -1, 0], !![1, -3, 5; -1, -3, -2; 1, 0, -1]⟩, Q₁),
  (⟨![7, 1, 2], !![-1, -1, -7; 2, -1, -1; 1, 1, -2], ![2, 2, 2], ![2, 0, 0], !![9, 1, 10; 9, -1, 11; 9, 0, 9], ![-2, -2, -2], ![0, 0, -1], !![-1, 3, 2; -1, -3, 5; -1, 0, -1]⟩, Q₁)]

theorem certsQ₁_valid : ∀ c ∈ certsQ₁, c.1.Valid Q₁ c.2 3 := by decide
theorem certsQ₂_valid : ∀ c ∈ certsQ₂, c.1.Valid Q₂ c.2 3 := by decide

theorem certsQ₁_cover : ∀ u ∈ Gen.allVecs 3 3, (∃ i, ¬ ((3 : ℕ) : ℤ) ∣ u i) → ((3 : ℕ) : ℤ) ∣ Q₁.eval u →
    ∃ c ∈ certsQ₁, ∃ a < (3 : ℕ), ∀ i, ((3 : ℕ) : ℤ) ∣ u i - (a : ℤ) * c.1.v i := by decide

theorem certsQ₂_cover : ∀ u ∈ Gen.allVecs 3 3, (∃ i, ¬ ((3 : ℕ) : ℤ) ∣ u i) → ((3 : ℕ) : ℤ) ∣ Q₂.eval u →
    ∃ c ∈ certsQ₂, ∃ a < (3 : ℕ), ∀ i, ((3 : ℕ) : ℤ) ∣ u i - (a : ℤ) * c.1.v i := by decide

/-- **$Q_2$ is in the genus of $Q_1$** (it is a $3$-neighbour form of $Q_1$; certificate). -/
@[kb "kneser1957" "§2, neighbour enumeration [unverified]"]
theorem sameGenus_Q₁_Q₂ : SameGenus Q₁ Q₂ :=
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  NbCert.sameGenus (c := (certsQ₁.head (by simp [certsQ₁])).1) (by norm_num) not_three_dvd_det_Q₁ (by decide)

/-- **$|\mathrm{Aut}(Q_1)| = 16$** (certified enumeration). -/
@[kb "scharlauhemkemeier1998" "§2 (automorphism groups) [unverified]"]
theorem card_aut_Q₁ : Nat.card (Aut Q₁) = 16 :=
  card_aut_eq_of_cert posDef_Q₁ (C := !![28, 0, 0; 0, 28, 0; 0, 0, 4]) (D := 56) (B := 2) (by decide) (by norm_num)
    (by decide) [!![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, 1], !![0, 1, 0; -1, 0, 0; 0, 0, -1], !![0, 1, 0; -1, 0, 0; 0, 0, 1], !![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, -1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, -1, 0; 1, 0, 0; 0, 0, -1], !![0, -1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- **$|\mathrm{Aut}(Q_2)| = 8$** (certified enumeration). -/
@[kb "scharlauhemkemeier1998" "§2 (automorphism groups) [unverified]"]
theorem card_aut_Q₂ : Nat.card (Aut Q₂) = 8 :=
  card_aut_eq_of_cert posDef_Q₂ (C := !![28, 0, 0; 0, 16, 4; 0, 4, 8]) (D := 56) (B := 2) (by decide) (by norm_num)
    (by decide) [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 1; 0, 0, 1], !![-1, 0, 0; 0, 1, -1; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, -1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, -1; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- **$Q_1 \not\sim Q_2$** (different automorphism counts). -/
theorem not_intEquiv_Q₁_Q₂ : ¬ IntEquiv Q₁ Q₂ := fun h => by
  have := card_aut_eq_of_intEquiv h
  rw [card_aut_Q₁, card_aut_Q₂] at this
  norm_num at this

/-- The two classes found, as a family indexed by `Fin 2`. -/
def reps : Fin 2 → QuadForm ℤ 3 := ![Q₁, Q₂]

theorem reps_distinct : ∀ i j, IntEquiv (reps i) (reps j) → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h not_intEquiv_Q₁_Q₂
  · exact absurd (IsometricGL.symm h) not_intEquiv_Q₁_Q₂
  · rfl

theorem sum_reps : ∑ i, ((Nat.card (Aut (reps i)) : ℝ))⁻¹ = 3 / 16 := by
  rw [Fin.sum_univ_two]
  simp only [reps, Matrix.cons_val_zero, Matrix.cons_val_one, card_aut_Q₁, card_aut_Q₂]
  norm_num

/-- **Mass lower bound:** $\mathrm{Mass}(Q_1) \ge 1/16 + 1/8 = 3/16$ (unconditional: two inequivalent classes found). -/
@[kb "schulzepillot1991" "§2 (mass check)"]
theorem mass_Q₁_ge : 3 / 16 ≤ mass Q₁ := by
  rw [← sum_reps]
  refine sum_inv_card_aut_le_mass posDef_Q₁ reps (fun i => ?_) reps_distinct
  fin_cases i
  · exact SameGenus.refl _
  · exact sameGenus_Q₁_Q₂

/-- **$\{Q_1, Q_2\}$ is closed under $3$-neighbour steps** (all $4 + 4$ isotropic lines certified). -/
@[kb "kneser1957" "§2, neighbour enumeration [unverified]"]
theorem nbrClosed_Q₁Q₂ : ∀ s ∈ [Q₁, Q₂], ∀ Q', IsNbrForm 3 s Q' → ∃ s' ∈ [Q₁, Q₂], IntEquiv s' Q' := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro s hs Q' h
  have hmem : ∀ cs : List (NbCert 3 × QuadForm ℤ 3), (∀ c ∈ cs, c.2 = Q₁ ∨ c.2 = Q₂) →
      ∀ c ∈ cs, c.2 ∈ [Q₁, Q₂] := by
    intro cs hcs c hc
    rcases hcs c hc with h | h <;> simp [h]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · obtain ⟨c, hc, he⟩ := exists_intEquiv_of_cover not_three_dvd_det_Q₁ certsQ₁ certsQ₁_valid certsQ₁_cover h
    exact ⟨c.2, hmem certsQ₁ (by
      intro c hc; simp only [certsQ₁, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact Or.inr rfl) c hc, he⟩
  · obtain ⟨c, hc, he⟩ := exists_intEquiv_of_cover not_three_dvd_det_Q₂ certsQ₂ certsQ₂_valid certsQ₂_cover h
    exact ⟨c.2, hmem certsQ₂ (by
      intro c hc; simp only [certsQ₂, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl) c hc, he⟩

/-- **The genus of $x_0^2 + x_1^2 + 7x_2^2$** (conditional on `KneserConnected 3 Q₁`, i.e. Kneser's theorem for this genus):
$\mathrm{Gen}(Q_1) = \{[Q_1], [Q_2]\}$ (class number $2$) and $\mathrm{Mass}(Q_1) = 1/16 + 1/8 = 3/16$. -/
@[kb "kneser1957" "§2 [unverified]"]
theorem genusClasses_Q₁_of_kneser (hK : KneserConnected 3 Q₁) :
    genusClasses Q₁ = Set.range (fun i => classOf (reps i)) ∧ mass Q₁ = 3 / 16 := by
  have hcl : genusClasses Q₁ = Set.range (fun i => classOf (reps i)) := by
    ext c
    induction c using Quotient.inductionOn with
    | h Q' =>
      change classOf Q' ∈ _ ↔ classOf Q' ∈ _
      rw [classOf_mem_genusClasses_iff]
      constructor
      · intro hg
        obtain ⟨s, hs, he⟩ := exists_intEquiv_of_closed hK [Q₁, Q₂] ⟨Q₁, by simp, IsometricGL.refl _⟩
          nbrClosed_Q₁Q₂ hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨0, classOf_eq_classOf_iff.mpr he⟩
        · exact ⟨1, classOf_eq_classOf_iff.mpr he⟩
      · rintro ⟨i, hi⟩
        have := classOf_eq_classOf_iff.mp hi
        refine (SameGenus.trans ?_ this.sameGenus)
        fin_cases i
        · exact SameGenus.refl _
        · exact sameGenus_Q₁_Q₂
  refine ⟨hcl, ?_⟩
  have hF := genusFinite posDef_Q₁
  rw [mass, hcl, ← sum_reps]
  classical
  rw [show Set.range (fun i => classOf (reps i)) = ((Finset.univ.image fun i => classOf (reps i)) : Set (QClass 3)) by
      simp, finsum_mem_coe_finset,
    Finset.sum_image (fun i _ j _ h => reps_distinct i j (classOf_eq_classOf_iff.mp h))]
  rfl

end QuadFormsKB.Siegel.Kneser.Examples
