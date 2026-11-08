/-
# Watson (1962, 1963): the rank of a form modulo a prime

Watson, *Transformations of a quadratic form which do not increase the class-number*, Proc. London Math. Soc. (3) 12
(1962), §2, and *The class-number of a positive quadratic form*, ibid. 13 (1963), §2: the *rank modulo $p$*
$r_p(f)$ of an integral form $f$ in $n$ variables. Watson defines it as the least $r$ such that the class of $f$
contains a form $f_1(x_1, \dots, x_r) + p(\dots)$ ((2.6) of 1962); equivalently (1962, Lemma 5) as the greatest $r$ for
which $f$ has an $r$-ary section with discriminant prime to $p$. Here it is defined intrinsically, through the
*radical of $f$ modulo $p$*
$$R_p(f) = \{\bar x \in \mathbb F_p^n : \bar f(\bar x + \bar z) = \bar f(\bar z) \text{ for all } \bar z \in \mathbb F_p^n\}
  = \{\bar x : \bar f(\bar x) = 0,\ \bar B(\bar x, \cdot) = 0\},$$
($\bar f$ the reduction of $f$, $\bar B$ its polar form), as $r_p(f) = n - \dim_{\mathbb F_p} R_p(f)$. The preimage of
$R_p(f)$ in $\mathbb Z^n$ is Watson's lattice $\Lambda_p(f)$ (`watsonSub`, his (2.4) with $m = p$).

**Proved here.**
* `radModP`, `rankModP`; `mem_radModP_iff` (the description by $\bar f(\bar x + \bar z) = \bar f(\bar z)$).
* `rankModP_le_of_repOver`: if $f$ represents $\varphi$ over $\mathbb F_p$, then $r_p(\varphi) \le r_p(f)$; with
  `RepOver.toZMod` and `Rep.repOver`, the same for representations over $\mathbb Z_p$ and over $\mathbb Z$.
* `rankModP_eq_of_sameGenus`: $r_p$ is an invariant of the genus.
* `rankModP_eq_of_not_dvd_det`: $r_p(f) = n$ if $p \nmid \det H_f$.
* `le_rankModP_orthSum`: $r_p(g \perp \psi) \ge r_p(g) + r_p(\psi)$ when $\bar g$ vanishes on the radical of
  $\bar B_g$ (always for odd $p$; Watson's (4.6) with his condition (4.1)).
-/
import QuadFormsKB.Literature.Watson1963.Perfect

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n v : ℕ} (p : ℕ) [Fact p.Prime]

/-! ### The radical modulo p -/

/-- Helper: the polar identity over any commutative ring $S$:
$Q(\vec x + \vec z) = Q(\vec x) + Q(\vec z) + \vec x^{\mathsf T} H \vec z$. -/
theorem evalIn_add' {S : Type*} [CommRing S] (Q : QuadForm ℤ n) (x z : Fin n → S) :
    Q.evalIn S (x + z) = Q.evalIn S x + Q.evalIn S z + x ⬝ᵥ (Q.hessian.map (algebraMap ℤ S) *ᵥ z) := by
  have := QuadForm.polar_eq_hessian S Q x z
  linear_combination this

/-- Helper: $Q(c\vec x) = c^2 Q(\vec x)$ over any commutative ring. -/
theorem evalIn_smul' {S : Type*} [CommRing S] (Q : QuadForm ℤ n) (c : S) (x : Fin n → S) :
    Q.evalIn S (c • x) = c ^ 2 * Q.evalIn S x := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **The radical of $f$ modulo $p$** (Watson 1962, (2.4) with $m = p$, reduced modulo $p$):
$R_p(f) = \{\bar x \in \mathbb F_p^n : \bar f(\bar x) = 0 \text{ and } \bar x^{\mathsf T} \bar H \bar z = 0 \ \forall
\bar z\}$, where $\bar f$ and $\bar H$ are $f$ and its Hessian reduced modulo $p$. An $\mathbb F_p$-subspace.
Arguments: the prime `p`, the form `f`. -/
@[kb "watson1962" "§2, (2.4), p. 578 (the lattice Λ_m(f), m = p, modulo p)"]
def radModP (f : QuadForm ℤ n) : Submodule (ZMod p) (Fin n → ZMod p) where
  carrier := {x | f.evalIn (ZMod p) x = 0 ∧ ∀ z, x ⬝ᵥ (f.hessian.map (algebraMap ℤ (ZMod p)) *ᵥ z) = 0}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [evalIn_add', hx0, hy0, hx]; ring
    · rw [add_dotProduct, hx, hy, add_zero]
  zero_mem' := ⟨by simp [QuadForm.evalIn], fun z => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx0, hx⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [evalIn_smul', hx0, mul_zero]
    · rw [smul_dotProduct, hx, smul_zero]

theorem mem_radModP {f : QuadForm ℤ n} {x : Fin n → ZMod p} :
    x ∈ radModP p f ↔ f.evalIn (ZMod p) x = 0 ∧ ∀ z, x ⬝ᵥ (f.hessian.map (algebraMap ℤ (ZMod p)) *ᵥ z) = 0 :=
  Iff.rfl

/-- **The radical modulo $p$ is Watson's condition (2.4):** $\bar x \in R_p(f)$ iff
$\bar f(\bar x + \bar z) = \bar f(\bar z)$ for all $\bar z$. -/
theorem mem_radModP_iff {f : QuadForm ℤ n} {x : Fin n → ZMod p} :
    x ∈ radModP p f ↔ ∀ z, f.evalIn (ZMod p) (x + z) = f.evalIn (ZMod p) z := by
  constructor
  · rintro ⟨hx0, hx⟩ z
    rw [evalIn_add', hx0, hx]; ring
  · intro h
    have h0 : f.evalIn (ZMod p) x = 0 := by
      have := h 0
      rwa [add_zero, evalIn_zero', ] at this
    refine ⟨h0, fun z => ?_⟩
    have := h z
    rw [evalIn_add', h0] at this
    linear_combination this

/-- **Watson's rank modulo $p$** (Watson 1962, §2, p. 579; 1963, §2, p. 551):
$r_p(f) = n - \dim_{\mathbb F_p} R_p(f)$ (`radModP`). Arguments: the prime `p`, the form `f`. -/
@[kb "watson1963" "§2, p. 551 (r = r_p(f), the rank of f modulo p)"]
def rankModP (f : QuadForm ℤ n) : ℕ := n - Module.finrank (ZMod p) (radModP p f)

theorem finrank_radModP_le (f : QuadForm ℤ n) : Module.finrank (ZMod p) (radModP p f) ≤ n := by
  have := Submodule.finrank_le (radModP p f)
  simpa using this

theorem rankModP_add_finrank (f : QuadForm ℤ n) :
    rankModP p f + Module.finrank (ZMod p) (radModP p f) = n := by
  have := finrank_radModP_le p f
  unfold rankModP; omega

theorem rankModP_le (f : QuadForm ℤ n) : rankModP p f ≤ n := by
  unfold rankModP; omega

/-! ### Monotonicity under representations -/

/-- **Representations do not decrease the rank modulo $p$:** if $f$ (in $n$ variables) represents $\varphi$ (in $v$
variables) over $\mathbb F_p$, then $r_p(\varphi) \le r_p(f)$. *Proof:* the matrix $\bar H$ maps the preimage of
$R_p(f)$ into $R_p(\varphi)$, and the preimage has dimension at least $v - (n - \dim R_p(f))$. Arguments: `h` the
representation over $\mathbb F_p$. -/
theorem rankModP_le_of_repOver {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : RepOver (ZMod p) f φ) :
    rankModP p φ ≤ rankModP p f := by
  classical
  obtain ⟨H, hH⟩ := h
  let L : (Fin v → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) := Matrix.mulVecLin H
  have hle : (radModP p f).comap L ≤ radModP p φ := by
    intro y hy
    rw [Submodule.mem_comap] at hy
    rw [mem_radModP_iff] at hy ⊢
    intro z
    have := hy (H *ᵥ z)
    rw [← hH, ← hH, mulVec_add]
    exact this
  -- the composite to the quotient has kernel the comap
  let π := (radModP p f).mkQ
  have hker : LinearMap.ker (π ∘ₗ L) = (radModP p f).comap L := by
    ext y
    simp [π, Submodule.mem_comap]
  have h1 := LinearMap.finrank_range_add_finrank_ker (π ∘ₗ L)
  have h2 : Module.finrank (ZMod p) (LinearMap.range (π ∘ₗ L)) ≤
      Module.finrank (ZMod p) ((Fin n → ZMod p) ⧸ radModP p f) := Submodule.finrank_le _
  have h3 := Submodule.finrank_quotient_add_finrank (radModP p f)
  have h4 : Module.finrank (ZMod p) ((radModP p f).comap L) ≤ Module.finrank (ZMod p) (radModP p φ) :=
    Submodule.finrank_mono hle
  rw [hker] at h1
  simp only [Module.finrank_fin_fun] at h1 h3
  have e1 := rankModP_add_finrank p f
  have e2 := rankModP_add_finrank p φ
  omega

/-- Helper: a ring homomorphism commutes with evaluation of an integral form. -/
theorem map_evalIn_hom {A B : Type*} [CommRing A] [CommRing B] (σ : A →+* B) (f : QuadForm ℤ n)
    (x : Fin n → A) : σ (f.evalIn A x) = f.evalIn B (fun i => σ (x i)) := by
  simp [QuadForm.evalIn, map_sum, apply_ite σ, map_mul]

/-- **A representation over $\mathbb Z_p$ reduces to one over $\mathbb F_p$.** -/
theorem RepOver.toZMod {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : RepOver ℤ_[p] f φ) :
    RepOver (ZMod p) f φ := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.map PadicInt.toZMod, fun y => ?_⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Fin v → ℤ_[p], ∀ i, PadicInt.toZMod (y' i) = y i := by
    choose y' hy' using fun i => ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) (y i)
    exact ⟨y', hy'⟩
  have e1 := map_evalIn_hom (PadicInt.toZMod (p := p)) f (H *ᵥ y')
  have e2 := map_evalIn_hom (PadicInt.toZMod (p := p)) φ y'
  rw [hH] at e1
  have hy : (fun i => PadicInt.toZMod (y' i)) = y := funext hy'
  rw [hy] at e2
  rw [← e2, e1]
  congr 1
  funext i
  simp [mulVec, dotProduct, map_sum, hy']

/-- **Local representations do not decrease the rank modulo $p$.** -/
theorem rankModP_le_of_repOver_padic {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : RepOver ℤ_[p] f φ) :
    rankModP p φ ≤ rankModP p f :=
  rankModP_le_of_repOver p (RepOver.toZMod p h)

/-- **Integral representations do not decrease the rank modulo $p$.** -/
theorem rankModP_le_of_rep {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (h : Rep f φ) :
    rankModP p φ ≤ rankModP p f :=
  rankModP_le_of_repOver p (h.repOver (ZMod p))

/-- Helper: `IsometricGL` of the base changes to $\mathbb Z_p$ is a representation over $\mathbb Z_p$. -/
theorem repOver_padic_of_isometricGL {f f' : QuadForm ℤ n}
    (h : IsometricGL (f.map (Int.castRingHom ℤ_[p])) (f'.map (Int.castRingHom ℤ_[p]))) : RepOver ℤ_[p] f f' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g.val, fun y => ?_⟩
  have e : ∀ (Q : QuadForm ℤ n) (x : Fin n → ℤ_[p]), (Q.map (Int.castRingHom ℤ_[p])).eval x = Q.evalIn ℤ_[p] x := by
    intro Q x
    simp [QuadForm.evalIn, QuadForm.map]
  rw [← e, ← e]
  exact hg y

/-- **The rank modulo $p$ is an invariant of the genus.** -/
theorem rankModP_eq_of_sameGenus {f f' : QuadForm ℤ n} (h : SameGenus f f') : rankModP p f = rankModP p f' :=
  le_antisymm (rankModP_le_of_repOver_padic p (repOver_padic_of_isometricGL p (h.1 p).symm))
    (rankModP_le_of_repOver_padic p (repOver_padic_of_isometricGL p (h.1 p)))

/-- **The rank modulo $p$ is an invariant of the class.** -/
theorem rankModP_eq_of_intEquiv {f f' : QuadForm ℤ n} (h : IntEquiv f f') : rankModP p f = rankModP p f' :=
  rankModP_eq_of_sameGenus p h.sameGenus

/-- **Full rank modulo $p$ when $p \nmid \det H$:** then $\bar H$ is invertible, so $R_p(f) = 0$ and
$r_p(f) = n$. -/
theorem rankModP_eq_of_not_dvd_det {f : QuadForm ℤ n} (h : ¬ (p : ℤ) ∣ f.hessian.det) : rankModP p f = n := by
  have hbot : radModP p f = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨-, hx⟩ := hx
    set M := f.hessian.map (algebraMap ℤ (ZMod p))
    have hdet : IsUnit M.det := by
      rw [isUnit_iff_ne_zero]
      have : M.det = ((f.hessian.det : ℤ) : ZMod p) := by
        rw [show M = (Int.castRingHom (ZMod p)).mapMatrix f.hessian from rfl, ← RingHom.map_det]
        rfl
      rw [this, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h
    -- xᵀ M = 0, so x = 0
    have hv : x ᵥ* M = 0 := by
      funext j
      have := hx (Pi.single j 1)
      rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
      simpa using this
    have := congrArg (· ᵥ* M⁻¹) hv
    simp only [vecMul_vecMul, mul_nonsing_inv _ hdet, vecMul_one, zero_vecMul] at this
    exact this
  unfold rankModP
  rw [hbot, finrank_bot]
  simp

/-! ### Orthogonal sums -/

/-- **Lower bound for the rank of an orthogonal sum** (Watson 1963, (4.6) and (9.3)): if $\bar g$ vanishes on the
radical of the polar form $\bar B_g$ (always true for odd $p$, since $2\bar g(\bar x) = \bar B_g(\bar x, \bar x)$),
then $R_p(g \perp \psi) \subseteq R_p(g) \times R_p(\psi)$, so $r_p(g \perp \psi) \ge r_p(g) + r_p(\psi)$.
Arguments: `hg` the condition on $g$. -/
theorem le_rankModP_orthSum {k m : ℕ} (g : QuadForm ℤ k) (ψ : QuadForm ℤ m)
    (hg : ∀ x : Fin k → ZMod p, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod p)) *ᵥ z) = 0) →
      g.evalIn (ZMod p) x = 0) :
    rankModP p g + rankModP p ψ ≤ rankModP p (QuadForm.orthSum g ψ) := by
  classical
  -- the two coordinate projections
  let π₁ : (Fin (k + m) → ZMod p) →ₗ[ZMod p] (Fin k → ZMod p) :=
    LinearMap.pi fun a => LinearMap.proj (Fin.castAdd m a)
  let π₂ : (Fin (k + m) → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p) :=
    LinearMap.pi fun b => LinearMap.proj (Fin.natAdd k b)
  let π : (Fin (k + m) → ZMod p) →ₗ[ZMod p] (Fin k → ZMod p) × (Fin m → ZMod p) := LinearMap.prod π₁ π₂
  have hπinj : Function.Injective π := by
    intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · exact congrFun h1 a
    · exact congrFun h2 b
  -- membership of the projections
  have hmem : ∀ x ∈ radModP p (QuadForm.orthSum g ψ), π₁ x ∈ radModP p g ∧ π₂ x ∈ radModP p ψ := by
    intro x hx
    rw [mem_radModP_iff] at hx
    -- values of the sum split
    have hsplit : ∀ y : Fin (k + m) → ZMod p, (QuadForm.orthSum g ψ).evalIn (ZMod p) y =
        g.evalIn (ZMod p) (π₁ y) + ψ.evalIn (ZMod p) (π₂ y) := fun y => evalIn_orthSum' g ψ y
    have hcomb : ∀ (a : Fin k → ZMod p) (b : Fin m → ZMod p), ∃ y : Fin (k + m) → ZMod p,
        π₁ y = a ∧ π₂ y = b := fun a b => ⟨Fin.append a b, by
          constructor <;> funext i <;> simp [π₁, π₂]⟩
    have hx' : ∀ a b, g.evalIn (ZMod p) (π₁ x + a) + ψ.evalIn (ZMod p) (π₂ x + b) =
        g.evalIn (ZMod p) a + ψ.evalIn (ZMod p) b := by
      intro a b
      obtain ⟨y, hy1, hy2⟩ := hcomb a b
      have := hx y
      rw [hsplit, hsplit, map_add, map_add, hy1, hy2] at this
      exact this
    -- the first component is in the radical of the polar form of g
    have hB : ∀ z, π₁ x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod p)) *ᵥ z) = 0 := by
      intro z
      have e1 := hx' z 0
      have e0 := hx' 0 0
      simp only [add_zero, zero_add, evalIn_zero'] at e0 e1
      rw [evalIn_add'] at e1
      linear_combination e1 - e0
    have hg0 : g.evalIn (ZMod p) (π₁ x) = 0 := hg _ hB
    have h1 : π₁ x ∈ radModP p g := ⟨hg0, hB⟩
    have h2 : π₂ x ∈ radModP p ψ := by
      rw [mem_radModP_iff]
      intro b
      have := hx' 0 b
      rw [add_zero, hg0, evalIn_zero', zero_add, zero_add] at this
      exact this
    exact ⟨h1, h2⟩
  let Lr : radModP p (QuadForm.orthSum g ψ) →ₗ[ZMod p] radModP p g × radModP p ψ :=
    LinearMap.prod (π₁.restrict fun x hx => (hmem x hx).1) (π₂.restrict fun x hx => (hmem x hx).2)
  have hLr : Function.Injective Lr := by
    intro x y hxy
    apply Subtype.ext
    apply hπinj
    have h1 : π₁ x = π₁ y := congrArg (fun z => (z.1 : Fin k → ZMod p)) hxy
    have h2 : π₂ x = π₂ y := congrArg (fun z => (z.2 : Fin m → ZMod p)) hxy
    exact Prod.ext h1 h2
  have hdim := LinearMap.finrank_le_finrank_of_injective hLr
  rw [Module.finrank_prod] at hdim
  have e1 := rankModP_add_finrank p g
  have e2 := rankModP_add_finrank p ψ
  have e3 := rankModP_add_finrank p (QuadForm.orthSum g ψ)
  omega

/-- **For odd $p$ the rank modulo $p$ of an orthogonal sum is at least the sum of the ranks.** -/
theorem le_rankModP_orthSum_of_odd {k m : ℕ} (hp : p ≠ 2) (g : QuadForm ℤ k) (ψ : QuadForm ℤ m) :
    rankModP p g + rankModP p ψ ≤ rankModP p (QuadForm.orthSum g ψ) := by
  refine le_rankModP_orthSum p g ψ fun x hx => ?_
  have h := hx x
  have e := QuadForm.polar_eq_hessian (ZMod p) g x x
  rw [h] at e
  have h2 : (2 : ZMod p) * g.evalIn (ZMod p) x = 0 := by
    rw [two_mul, ← two_smul (ZMod p) x, evalIn_smul'] at *
    linear_combination e
  have h2' : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
    exact hp this
  exact (mul_eq_zero.mp h2).resolve_left h2'

end QuadFormsKB.Watson1963
