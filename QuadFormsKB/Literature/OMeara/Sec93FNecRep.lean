/-
# O'Meara 93:28, proof of the necessity, step 1: the special case, condition (iii)

**Setting** (as in `Sec93FNecBase.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction
field $F$, $2 \ne 0$ in $R$ and not a unit; $(V, Q)$ a quadratic space over $F$; lattices `Submodule R V`. Indices are
$0$-based: O'Meara's $L_1$, $L_2$, $\mathfrak f_1$, $a_1$ are `Ls i₀`, `Ls i₁`, `fIdeal Q L Ls i₀ i₁`, `a i₀`.

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity, step 1, pp. 269–270, condition (iii))
* `round_step`: the quadratic-space heart of O'Meara's argument "by Example 93:17 ... $\langle A(2a_1\alpha^2 + \beta,
  \gamma)\rangle$ is isotropic by the Local Square Theorem". In a quadratic space, if $y_0, y_1, z$ have the Gram data
  $Q(y_0) = a_0\alpha^2 + \beta$ with $\beta \in \mathfrak w$, $Q(y_0) \in a_0\mathfrak o^\times$, $B(y_0, y_1)^2 - Q(y_0)Q(y_1)
  \cong 1 \bmod \mathfrak f$ with $\mathfrak f \subsetneq 4a_0\mathfrak w^{-1}$, $z \perp y_0, y_1$ and $Q(z) \in a_0 + \mathfrak w$,
  then $\operatorname{span}\{y_0, y_1, z\}$ contains a hyperbolic pair $r_1, r_2$ and a vector $z' \perp r_1, r_2$ with
  $Q(z') \in a_0 + \mathfrak w$ again. (Hence the argument can be repeated.)
* `nec_base_rep`: condition (iii) of 93:28 in the special case.

The 93:17 normal form is not used: the vector $q = \kappa y_0 + \theta y_1$ with $B(y_0, q) = 1$ and $Q(q) =
(1 - \theta^2\delta)/Q(y_0)$ plays the role of its second base vector (only the quadratic space matters here).
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecBase

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecBase

open Sat93 Arith28 D18

section Plane

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {W : Type*} [AddCommGroup W] [Module F W]
variable (QW : QuadraticForm F W)

/-- **A hyperbolic partner**: if $r_1$ is isotropic and $B(r_1, w) = b \ne 0$, then $r_2 = b^{-1}(w - \tfrac{Q(w)}{2b}r_1)$
is isotropic with $B(r_1, r_2) = 1$. -/
theorem hyp_partner {r₁ w : W} (h1 : QW r₁ = 0) (hb : bil QW r₁ w ≠ 0) :
    ∃ c₁ c₂ : F, QW (c₁ • w + c₂ • r₁) = 0 ∧ bil QW r₁ (c₁ • w + c₂ • r₁) = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  refine ⟨(bil QW r₁ w)⁻¹, -(QW w) / (2 * bil QW r₁ w ^ 2), ?_, ?_⟩
  · rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, bil_comm QW w r₁, h1]
    field_simp
    ring
  · rw [bil_add_right, bil_smul_right, bil_smul_right, bil_self, h1]
    field_simp
    ring

/-- The isotropic vector of a plane $\begin{pmatrix} m & 1\\ 1 & \gamma\end{pmatrix}$: with $(\nu - 1)^2 = 1 - m\gamma$,
$\gamma + 2\mu + m\mu^2 = 0$ for $\mu = -\gamma/\nu$. -/
theorem iso_aux {γ m ν : F} (hν : ν ≠ 0) (h : (ν - 1) ^ 2 = 1 - m * γ) :
    γ + 2 * (-γ / ν) + (-γ / ν) ^ 2 * m = 0 := by
  field_simp
  linear_combination γ * h

end Plane

section Round

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {W : Type*} [AddCommGroup W] [Module F W]
variable (QW : QuadraticForm F W)

/-- A unit plus an element of the maximal ideal is a unit. -/
theorem isUnit_one_add_mem {z : R} (hz : z ∈ maximalIdeal R) : IsUnit (1 + z) := by
  by_contra h
  have hm : 1 + z ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have : (1 : R) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hm hz
  exact ((IsLocalRing.mem_maximalIdeal _).1 this) isUnit_one

/-- **One round of O'Meara's argument** (p. 270): see the file header. -/
theorem round_step (h2p : ¬ IsUnit (2 : R)) {a₀ w : F} (ha0 : a₀ ≠ 0) (hw0 : w ≠ 0)
    (ha0R : ∃ r : R, algebraMap R F r = a₀) (hw1 : ∃ r : R, algebraMap R F r = w)
    (hw2 : ∃ r : R, algebraMap R F r * w = 2) {𝔣 : Submodule R F}
    (hf : ∀ x ∈ 𝔣, ∃ ρ ∈ maximalIdeal R, x = algebraMap R F ρ * (4 * a₀ / w))
    {y₀ y₁ z : W} (hA : ∃ u : R, IsUnit u ∧ QW y₀ = a₀ * algebraMap R F u)
    (hAα : ∃ α b : R, QW y₀ = a₀ * algebraMap R F α ^ 2 + w * algebraMap R F b)
    (hδ : ∃ ε : R, IsUnit ε ∧ ∃ x ∈ 𝔣, bil QW y₀ y₁ ^ 2 - QW y₀ * QW y₁ = algebraMap R F ε ^ 2 + x)
    (hz₀ : bil QW y₀ z = 0) (hz₁ : bil QW y₁ z = 0) (hc : ∃ b : R, QW z = a₀ + w * algebraMap R F b) :
    ∃ r₁ r₂ z' : W, (∀ S : Submodule F W, y₀ ∈ S → y₁ ∈ S → z ∈ S → r₁ ∈ S ∧ r₂ ∈ S ∧ z' ∈ S) ∧
      QW r₁ = 0 ∧ QW r₂ = 0 ∧ bil QW r₁ r₂ = 1 ∧ bil QW r₁ z' = 0 ∧ bil QW r₂ z' = 0 ∧
      ∃ b : R, QW z' = a₀ + w * algebraMap R F b := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  obtain ⟨a0r, rfl⟩ := ha0R
  obtain ⟨wr, rfl⟩ := hw1
  obtain ⟨tr, htr⟩ := hw2
  obtain ⟨u, hu, hAu⟩ := hA
  obtain ⟨α, b₁, hAα⟩ := hAα
  obtain ⟨ε, hε, x, hx, hδ'⟩ := hδ
  obtain ⟨ρ, hρ, hxρ⟩ := hf x hx
  obtain ⟨b₂, hb₂⟩ := hc
  obtain ⟨ε', hεε'⟩ := hε.exists_right_inv
  obtain ⟨u', huu'⟩ := hu.exists_right_inv
  have hεε'F : algebraMap R F ε * algebraMap R F ε' = 1 := by rw [← map_mul, hεε', map_one]
  have huu'F : algebraMap R F u * algebraMap R F u' = 1 := by rw [← map_mul, huu', map_one]
  have hAne : QW y₀ ≠ 0 := by
    rw [hAu]
    refine mul_ne_zero ha0 fun h => ?_
    rw [h, zero_mul] at huu'F
    exact zero_ne_one huu'F
  set A := QW y₀ with hAdef
  set Bv := bil QW y₀ y₁ with hBvdef
  set C := QW y₁ with hCdef
  set c := QW z with hcdef
  set θ : F := algebraMap R F ε' with hθ
  have hθε : θ * algebraMap R F ε = 1 := by rw [mul_comm]; exact hεε'F
  obtain ⟨κ, hκ⟩ : ∃ κ : F, κ * A = 1 - θ * Bv := ⟨(1 - θ * Bv) / A, by field_simp⟩
  set P : W := y₀ + (algebraMap R F α) • z with hPdef
  set q : W := κ • y₀ + θ • y₁ with hqdef
  have hzy₀ : bil QW z y₀ = 0 := by rw [bil_comm]; exact hz₀
  have hzy₁ : bil QW z y₁ = 0 := by rw [bil_comm]; exact hz₁
  have hy₁y₀ : bil QW y₁ y₀ = Bv := bil_comm QW y₁ y₀
  have hPP : QW P = A + algebraMap R F α ^ 2 * c := by
    rw [hPdef, Q_add, bil_smul_right, hz₀, Q_smul]; ring
  have hPq : bil QW P q = 1 := by
    rw [hPdef, hqdef]
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, bil_self, hz₀, hz₁, hzy₀, hzy₁,
      hy₁y₀]
    linear_combination hκ
  have hQq : QW q = κ ^ 2 * A + 2 * κ * θ * Bv + θ ^ 2 * C := by
    rw [hqdef, Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right]; ring
  have hzP : bil QW z P = algebraMap R F α * c := by
    rw [hPdef]; simp only [bil_add_right, bil_smul_right, hzy₀, bil_self]; ring
  have hzq : bil QW z q = 0 := by
    rw [hqdef]; simp only [bil_add_right, bil_smul_right, hzy₀, hzy₁]; ring
  have hAγ : A * QW q = -(θ ^ 2 * x) := by
    rw [hQq]
    linear_combination (κ * A + 1 + θ * Bv) * hκ - θ ^ 2 * hδ' - (θ * algebraMap R F ε + 1) * hθε
  have hγ : QW q = -(θ ^ 2 * x) / A := by rw [eq_div_iff hAne, mul_comm]; exact hAγ
  have hu0 : algebraMap R F u ≠ 0 := fun h => by rw [h, zero_mul] at huu'F; exact zero_ne_one huu'F
  have hu'eq : algebraMap R F u' = (algebraMap R F u)⁻¹ := eq_inv_of_mul_eq_one_right huu'F
  -- the small scalars
  set ρ₂ : R := -(ε' * ε' * ρ * u') with hρ₂def
  have hρ₂ : ρ₂ ∈ maximalIdeal R :=
    (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hρ))
  have hγ' : QW q = 4 * algebraMap R F ρ₂ / algebraMap R F wr := by
    rw [hγ, hxρ, hAu, hρ₂def]
    simp only [map_neg, map_mul, hu'eq, hθ]
    field_simp
  set m₁ : R := tr * a0r * α ^ 2 + b₁ + α ^ 2 * b₂ with hm₁def
  have hm : QW P = algebraMap R F wr * algebraMap R F m₁ := by
    rw [hPP, hAα, hb₂, hm₁def]
    simp only [map_add, map_mul, map_pow]
    linear_combination (-(algebraMap R F a0r * algebraMap R F α ^ 2)) * htr
  have hmγ : QW P * QW q = 4 * algebraMap R F (m₁ * ρ₂) := by
    rw [hm, hγ', map_mul]; field_simp
  set ρ₃ : R := -(m₁ * ρ₂) with hρ₃def
  have hρ₃ : ρ₃ ∈ maximalIdeal R := (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ hρ₂)
  obtain ⟨s, hs⟩ := isSquare_one_add_four_mul hρ₃
  have hσu : IsUnit (1 + 4 * ρ₃) := isUnit_one_add_mem (Ideal.mul_mem_left _ _ hρ₃)
  have hsu : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ hσu)
  obtain ⟨s', hss'⟩ := hsu.exists_right_inv
  have hss'F : algebraMap R F s * algebraMap R F s' = 1 := by rw [← map_mul, hss', map_one]
  have hs0 : algebraMap R F s ≠ 0 := fun h => by rw [h, zero_mul] at hss'F; exact zero_ne_one hss'F
  have hσ : 1 - QW P * QW q = algebraMap R F s * algebraMap R F s := by
    rw [hmγ, ← map_mul, ← hs]
    simp only [hρ₃def, map_add, map_mul, map_neg, map_one, map_ofNat]; ring
  have hσ0 : algebraMap R F s * algebraMap R F s ≠ 0 := mul_ne_zero hs0 hs0
  obtain ⟨s₁, hs₁, hν⟩ : ∃ s₁ : F, s₁ ^ 2 = algebraMap R F s * algebraMap R F s ∧ 1 + s₁ ≠ 0 := by
    by_cases h : 1 + algebraMap R F s = 0
    · refine ⟨-algebraMap R F s, by ring, ?_⟩
      intro h'
      apply h2F
      linear_combination h + h'
    · exact ⟨algebraMap R F s, by ring, h⟩
  have hsq₁ : (1 + s₁ - 1) ^ 2 = 1 - QW P * QW q := by rw [hσ, ← hs₁]; ring
  have hPq' : bil QW q P = 1 := by rw [bil_comm]; exact hPq
  obtain ⟨μ, hμ⟩ : ∃ μ : F, μ = -(QW q) / (1 + s₁) := ⟨_, rfl⟩
  have hQr₁ : QW (q + μ • P) = 0 := by
    rw [Q_add, Q_smul, bil_smul_right, hPq', hμ]
    have := iso_aux (γ := QW q) (m := QW P) hν hsq₁
    linear_combination this
  have hb1 : bil QW (q + μ • P) P = 1 + μ * QW P := by
    rw [bil_add_left, bil_smul_left, hPq', bil_self]
  have hb2 : bil QW (q + μ • P) q = QW q + μ := by
    rw [bil_add_left, bil_smul_left, bil_self, hPq]; ring
  have hnz : bil QW (q + μ • P) P ≠ 0 ∨ bil QW (q + μ • P) q ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨h1', h2'⟩ := hcon
    rw [hb1] at h1'
    rw [hb2] at h2'
    apply hσ0
    rw [← hσ]
    linear_combination h1' - (QW P) * h2'
  obtain ⟨r₂, hr₂Q, hr₂B, c₁, c₂, hr₂eq⟩ : ∃ r₂ : W, QW r₂ = 0 ∧ bil QW (q + μ • P) r₂ = 1 ∧
      ∃ c₁ c₂ : F, r₂ = c₁ • P + c₂ • q := by
    rcases hnz with h | h
    · obtain ⟨d₁, d₂, h1, h2'⟩ := hyp_partner QW hQr₁ h
      exact ⟨d₁ • P + d₂ • (q + μ • P), h1, h2', d₁ + d₂ * μ, d₂, by module⟩
    · obtain ⟨d₁, d₂, h1, h2'⟩ := hyp_partner QW hQr₁ h
      exact ⟨d₁ • q + d₂ • (q + μ • P), h1, h2', d₂ * μ, d₁ + d₂, by module⟩
  -- the orthogonal complement vector
  obtain ⟨lam, hlam⟩ : ∃ lam : F, lam = algebraMap R F α * c * QW q /
      (algebraMap R F s * algebraMap R F s) := ⟨_, rfl⟩
  obtain ⟨nu2, hnu2⟩ : ∃ nu2 : F, nu2 = -(algebraMap R F α * c) /
      (algebraMap R F s * algebraMap R F s) := ⟨_, rfl⟩
  obtain ⟨z', hz'def⟩ : ∃ z' : W, z' = z + lam • P + nu2 • q := ⟨_, rfl⟩
  have hPz : bil QW P z = algebraMap R F α * c := by rw [bil_comm]; exact hzP
  have hqz : bil QW q z = 0 := by rw [bil_comm]; exact hzq
  have hz'P : bil QW z' P = 0 := by
    rw [hz'def]
    simp only [bil_add_left, bil_smul_left, hzP, bil_self, hPq']
    rw [hlam, hnu2]
    field_simp
    linear_combination (-(algebraMap R F α * c)) * hσ
  have hz'q : bil QW z' q = 0 := by
    rw [hz'def]
    simp only [bil_add_left, bil_smul_left, hzq, bil_self, hPq]
    rw [hlam, hnu2]
    field_simp
    ring
  have hQz' : QW z' = c + lam * (algebraMap R F α * c) := by
    have h1 : QW z' = bil QW z' z := by
      calc QW z' = bil QW z' z' := (bil_self QW z').symm
        _ = bil QW z' (z + lam • P + nu2 • q) := by rw [← hz'def]
        _ = bil QW z' z := by
          simp only [bil_add_right, bil_smul_right, hz'P, hz'q]; ring
    rw [h1, hz'def]
    simp only [bil_add_left, bil_smul_left, hPz, hqz, bil_self]
    ring
  have hS : ∀ S : Submodule F W, y₀ ∈ S → y₁ ∈ S → z ∈ S → P ∈ S ∧ q ∈ S := fun S h0 h1 hz =>
    ⟨add_mem h0 (smul_mem _ _ hz), add_mem (smul_mem _ _ h0) (smul_mem _ _ h1)⟩
  refine ⟨q + μ • P, r₂, z', ?_, hQr₁, hr₂Q, hr₂B, ?_, ?_, ?_⟩
  · intro S h0 h1 hz
    obtain ⟨hP, hq⟩ := hS S h0 h1 hz
    refine ⟨add_mem hq (smul_mem _ _ hP), ?_, ?_⟩
    · rw [hr₂eq]; exact add_mem (smul_mem _ _ hP) (smul_mem _ _ hq)
    · rw [hz'def]; exact add_mem (add_mem hz (smul_mem _ _ hP)) (smul_mem _ _ hq)
  · rw [bil_add_left, bil_smul_left, bil_comm QW q z', bil_comm QW P z', hz'q, hz'P]; ring
  · rw [hr₂eq, bil_add_left, bil_smul_left, bil_smul_left, bil_comm QW P z', bil_comm QW q z', hz'q, hz'P]
    ring
  · refine ⟨b₂ + α ^ 2 * (a0r + wr * b₂) ^ 2 * tr ^ 2 * ρ₂ * s' ^ 2, ?_⟩
    have hcF : c = algebraMap R F (a0r + wr * b₂) := by
      simp only [map_add, map_mul]; exact hb₂
    have h4 : (4 : F) = (algebraMap R F tr * algebraMap R F wr) ^ 2 := by rw [htr]; norm_num
    have hs'eq : algebraMap R F s' = (algebraMap R F s)⁻¹ := eq_inv_of_mul_eq_one_right hss'F
    rw [hQz', hlam, hγ', hcF, h4]
    simp only [map_add, map_mul, map_pow, hs'eq]
    field_simp
    ring

end Round

section Frame

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The quadratic space $FN \perp \langle c\rangle$ on $V \times F$: $(x, t) \mapsto Q(x) + c\,t^2$. -/
def repForm (c : F) : QuadraticForm F (V × F) := Q.prod (c • QuadraticMap.sq)

theorem repForm_apply (c : F) (p : V × F) : repForm Q c p = Q p.1 + c * (p.2 * p.2) := by
  simp [repForm, QuadraticMap.prod_apply]

theorem bil_repForm (c : F) (p p' : V × F) :
    bil (repForm Q c) p p' = bil Q p.1 p'.1 + c * (p.2 * p'.2) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  apply mul_left_cancel₀ h2
  have h := Q_add (repForm Q c) p p'
  rw [repForm_apply, repForm_apply, repForm_apply, Prod.fst_add, Prod.snd_add, Q_add Q] at h
  linear_combination -h

/-- **From a frame to `SpanRepresents`**: if $e$ is an $R$-base of $M$ with $\det(B(e_i, e_j)) \ne 0$, and there are
vectors $X_k = (u_k, t_k) \in V \times F$ with $u_k \in FN$ and $B(u_k, u_l) + c\,t_kt_l = B(e_k, e_l)$, then
$FM \to FN \perp \langle c \rangle$. -/
theorem spanRepresents_of_frame {n : ℕ} {M N : Submodule R V} (c : F) (e : Basis (Fin n) R M)
    (X : Fin n → V × F) (hX : ∀ k, (X k).1 ∈ span F (N : Set V))
    (hG : ∀ k l, bil Q (X k).1 (X l).1 + c * ((X k).2 * (X l).2) = gram Q (fun i => (e i : V)) k l)
    (hdet : (gram Q fun i => (e i : V)).det ≠ 0) : SpanRepresents Q M N c := by
  classical
  set v : Fin n → V := fun i => (e i : V) with hv
  have hliR : LinearIndependent R v := (e.linearIndependent).map' M.subtype (Submodule.ker_subtype M)
  have hliF : LinearIndependent F v := (LinearIndependent.iff_fractionRing R F).1 hliR
  have hspan : span F (Set.range v) = span F (M : Set V) := by
    apply le_antisymm
    · exact span_mono (by rintro _ ⟨i, rfl⟩; exact (e i).2)
    · refine span_le.2 fun m hm => ?_
      have h := e.sum_repr ⟨m, hm⟩
      have h' : m = ∑ i, e.repr ⟨m, hm⟩ i • v i := by
        have := congrArg (fun x : M => (x : V)) h
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      rw [h']
      refine sum_mem fun i _ => ?_
      rw [← algebraMap_smul F]
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  let b : Basis (Fin n) F (span F (M : Set V)) :=
    (Basis.span hliF).map (LinearEquiv.ofEq _ _ hspan)
  have hb : ∀ k, (b k : V) = v k := fun k => by simp [b, Basis.span_apply]
  let g : Fin n → span F (N : Set V) × F := fun k => (⟨(X k).1, hX k⟩, (X k).2)
  let f : span F (M : Set V) →ₗ[F] span F (N : Set V) × F := b.constr F g
  have hfb : ∀ k, f (b k) = g k := fun k => by simp [f]
  have hfx : ∀ x, f x = ∑ k, b.repr x k • g k := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hfb]
  have hfx' : ∀ x, (((f x).1 : V), (f x).2) = ∑ k, b.repr x k • X k := by
    intro x
    rw [hfx x]
    ext <;> simp [g, Prod.fst_sum, Prod.snd_sum]
  have hxv : ∀ x : span F (M : Set V), (x : V) = ∑ k, b.repr x k • v k := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, hb]
  have hgramW : gram (repForm Q c) X = gram Q v := by
    ext k l
    simp only [gram, Matrix.of_apply, bil_repForm]
    exact hG k l
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have h0 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    set d := x - y with hd
    have h1 : ∑ k, b.repr d k • X k = 0 := by
      rw [← hfx' d, h0]; rfl
    have h2 : b.repr d ᵥ* gram Q v = 0 := by
      funext l
      have : bil (repForm Q c) (∑ k, b.repr d k • X k) (X l) = 0 := by rw [h1]; simp [bil]
      rw [bil_sum_left] at this
      simp only [bil_smul_left] at this
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
      rw [← hgramW]
      simpa [gram] using this
    have h3 : ⇑(b.repr d) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h2
    have h4 : d = 0 := by
      rw [← b.sum_repr d]
      exact Finset.sum_eq_zero fun k _ => by rw [show b.repr d k = 0 from congrFun h3 k, zero_smul]
    exact sub_eq_zero.1 h4
  · intro x
    have e1 := congrArg (repForm Q c) (hfx' x)
    rw [repForm_apply] at e1
    have e2 : repForm Q c (∑ k, b.repr x k • X k) =
        b.repr x ⬝ᵥ gram (repForm Q c) X *ᵥ b.repr x := D18.Q_sum_gram (repForm Q c) X (b.repr x)
    have e3 : Q (x : V) = b.repr x ⬝ᵥ gram Q v *ᵥ b.repr x := by
      rw [hxv x]; exact D18.Q_sum_gram Q v _
    simp only at e1
    rw [e3, ← hgramW, ← e2, ← e1]; ring

end Frame

section Aux

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- A proper sub-ideal of $g\mathfrak o$ lies in $\mathfrak p g$. -/
theorem mem_p_mul_of_lt {𝔞 : Submodule R F} {g : F} (hlt : 𝔞 < R ∙ g) {x : F} (hx : x ∈ 𝔞) :
    ∃ ρ ∈ maximalIdeal R, x = algebraMap R F ρ * g := by
  obtain ⟨r, hr⟩ := mem_span_singleton.1 (hlt.le hx)
  refine ⟨r, ?_, by rw [← hr, Algebra.smul_def]⟩
  by_contra hrm
  have hu : IsUnit r := by
    by_contra h; exact hrm ((IsLocalRing.mem_maximalIdeal _).2 h)
  apply hlt.not_ge
  rw [span_singleton_le_iff_mem]
  obtain ⟨r', hr'⟩ := hu.exists_left_inv
  have : g = r' • x := by rw [← hr, smul_smul, hr', one_smul]
  rw [this]; exact 𝔞.smul_mem _ hx

/-- $g\cdot(\mathfrak o / w\mathfrak o) = g w^{-1}\mathfrak o$. -/
theorem smul_one_div_span {w : F} (hw : w ≠ 0) (g : F) :
    g • ((1 : Submodule R F) / (R ∙ w)) = R ∙ (g * w⁻¹) := by
  have h1 : (1 : Submodule R F) / (R ∙ w) = R ∙ w⁻¹ := by
    ext z
    rw [FIdealAux.mem_div_span_iff, Submodule.mem_one, mem_span_singleton]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [Algebra.smul_def, hr]; field_simp⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, by rw [Algebra.smul_def]; field_simp⟩
  rw [h1, Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul]

/-- A unit plus an element of the maximal ideal is a unit. -/
theorem isUnit_add_mem' {u z : R} (hu : IsUnit u) (hz : z ∈ maximalIdeal R) : IsUnit (u + z) := by
  by_contra h
  have hm : u + z ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have : u ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hm hz
  exact ((IsLocalRing.mem_maximalIdeal _).1 this) hu

end Aux

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]
  {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

set_option maxHeartbeats 3200000 in
/-- **93:28, necessity, step 1, condition (iii)** (O'Meara 1963, §93F, pp. 269–270). See the file header. -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, step 1, pp. 269–270 (condition (iii))"]
theorem nec_base_rep (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q L Ks)
    (i₀ i₁ : Fin t) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (hU : scale Q (Ls i₀) = 1) {a' a'' : F}
    (hblk : HasBlk Q (Ls i₀) a' 0 a'' 0) (ha' : IsNormGenerator Q (fundSub Q L Ls i₀) a')
    (ha'' : IsNormGenerator Q (fundSub Q L Ls i₀) a'')
    (hlt : fIdeal Q L Ls i₀ i₁ < (4 * a i₀) • (1 / fundWeight Q L Ls i₀)) :
    SpanRepresents Q (jordanChain Ls i₀) (jordanChain Ks i₀) (a i₀) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [jordanChain_zero Ls i₀ h₀, jordanChain_zero Ks i₀ h₀]
  have hreg := isRegular_of_isJordanSplitting Q hfg hL
  -- the Jordan types agree
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK
  have hc : ∀ i, Fin.cast hT i = i := fun i => Fin.ext (by simp)
  have hsc : ∀ i, scale Q (Ls i) = scale Q (Ks i) := fun i => by have := (hJT i).1; rwa [hc] at this
  have hK0 : scale Q (Ks i₀) = 1 := (hsc i₀) ▸ hU
  have hKi₁ : Ks i₁ ≤ L := hK.split.iSup_eq ▸ le_iSup Ks i₁
  set s₂ := scale Q (Ks i₁) with hs₂def
  have hs₂lt : s₂ < 1 := hK0 ▸ hK.scale_strictAnti (Fin.lt_def.2 (by omega))
  have hs₂R : ∀ z ∈ s₂, ∃ r ∈ maximalIdeal R, algebraMap R F r = z := fun z hz =>
    exists_max_of_lt_one (scale_fg Q (FG.of_le hfg hKi₁)) (hK.modular i₁).1 hs₂lt hz
  have hs₂R' : ∀ z ∈ s₂, ∃ r : R, algebraMap R F r = z := fun z hz => by
    obtain ⟨r, -, hr⟩ := hs₂R z hz; exact ⟨r, hr⟩
  set g₁ := fundNormGroup Q L Ls i₀ with hg₁def
  set g₂ := fundNormGroup Q L Ls i₁ with hg₂def
  have hg₂ : g₂ = normGroup Q (subA Q s₂ L) := by rw [hg₂def, hs₂def, ← hsc i₁]; rfl
  have hg₂₁ : g₂ ≤ g₁ := fundNormGroup_antitone Q hL (Fin.le_def.2 (by omega))
  -- the base `x` of `L₁`
  obtain ⟨e, he⟩ := hblk
  set x : Fin 4 → V := fun k => (e k : V) with hxdef
  have hGx : ∀ k l, bil Q (x k) (x l) = blk2 a' 0 a'' 0 k l := fun k l => by
    have := congrFun (congrFun he k) l; simpa [gram] using this
  have hx00 : Q (x 0) = a' := by rw [← bil_self, hGx]; simp [blk2]
  have hx11 : Q (x 1) = 0 := by rw [← bil_self, hGx]; simp [blk2]
  have hx22 : Q (x 2) = a'' := by rw [← bil_self, hGx]; simp [blk2]
  have hx33 : Q (x 3) = 0 := by rw [← bil_self, hGx]; simp [blk2]
  have hx01 : bil Q (x 0) (x 1) = 1 := by rw [hGx]; simp [blk2]
  have hx23 : bil Q (x 2) (x 3) = 1 := by rw [hGx]; simp [blk2]
  have hx20 : bil Q (x 2) (x 0) = 0 := by rw [hGx]; simp [blk2]
  have hx21 : bil Q (x 2) (x 1) = 0 := by rw [hGx]; simp [blk2]
  have hx30 : bil Q (x 3) (x 0) = 0 := by rw [hGx]; simp [blk2]
  have hx31 : bil Q (x 3) (x 1) = 0 := by rw [hGx]; simp [blk2]
  -- `x_k = y_k + Y_k`
  have hLi : Ls i₀ ≤ L := hL.split.iSup_eq ▸ le_iSup Ls i₀
  have hdec : ∀ k, ∃ y ∈ Ks i₀, ∃ Y ∈ others Ks i₀, y + Y = x k := fun k =>
    mem_sup.mp ((sup_others Q hK.split i₀).symm ▸ hLi (e k).2)
  choose y hy Y hY hxy using hdec
  have hYsub : ∀ k, Y k ∈ subA Q s₂ L := fun k => mem_subA_of_others Q hK i₀ i₁ h₀ h₁ (hY k)
  have hyY : ∀ k l, bil Q (y k) (Y l) = 0 := fun k l => orth_others Q hK.split i₀ (hy k) (Y l) (hY l)
  have hB : ∀ k l, bil Q (x k) (x l) = bil Q (y k) (y l) + bil Q (Y k) (Y l) := by
    intro k l
    rw [← hxy k, ← hxy l, bil_add_left, bil_add_right, bil_add_right, hyY k l, bil_comm Q (Y k) (y l), hyY l k]
    ring
  have hQ : ∀ k, Q (x k) = Q (y k) + Q (Y k) := by
    intro k; rw [← hxy k, Q_add, hyY k k]; ring
  have hYY : ∀ k l, bil Q (Y k) (Y l) ∈ s₂ := fun k l => (hYsub k).2 _ (hYsub l).1
  have hQY : ∀ k, Q (Y k) ∈ g₂ := fun k => hg₂ ▸ Q_mem_normGroup Q (hYsub k)
  have hyR : ∀ {u v : V}, u ∈ Ks i₀ → v ∈ Ks i₀ → ∃ r : R, algebraMap R F r = bil Q u v := fun hu hv =>
    Submodule.mem_one.mp (hK0 ▸ bil_mem_scale Q hu hv)
  have hyL : ∀ {u : V}, u ∈ Ks i₀ → ∀ l ∈ L, ∃ r : R, algebraMap R F r = bil Q u l := by
    intro u hu l hl
    rw [← sup_others Q hK.split i₀] at hl
    obtain ⟨k, hk, o, ho, rfl⟩ := mem_sup.mp hl
    rw [bil_add_right, orth_others Q hK.split i₀ hu o ho, add_zero]
    exact hyR hu hk
  have hfs₀ : Ls i₀ ≤ fundSub Q L Ls i₀ := le_fundSub Q hfg hL i₀
  have hxg : ∀ k, Q (x k) ∈ g₁ := fun k => Q_mem_normGroup Q (hfs₀ (e k).2)
  have hn : ∀ i, fundNormIdeal Q L Ls i = R ∙ a i := fun i => (ha i).2.symm
  have hf : fIdeal Q L Ls i₀ i₁ = fIdealOf R (R ∙ (1 : F)) g₁ g₂ (R ∙ a i₀) (R ∙ a i₁) := by
    rw [fIdeal, hU, hn, hn, Submodule.one_eq_span]
  have ha0 : ∀ i, a i ≠ 0 := fun i =>
    (ha i).ne_zero Q (isRegular_fundSub Q hfg hreg hL i) (fundSub_ne_bot Q hfg hL i)
  have hgA : ∀ i, ∀ z ∈ fundNormGroup Q L Ls i, z ∈ R ∙ a i := fun i z hz =>
    (ha i).2 ▸ normGroup_subset_normIdeal Q _ hz
  have haS : ∀ i, a i ∈ scale Q (Ls i) := fun i => by
    rw [← scale_fundSub Q hfg hL i]
    exact normIdeal_le_scale Q _ ((ha i).2 ▸ mem_span_singleton_self (a i))
  have hu₀ : 0 ≤ dord hπ (a i₀) := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hU ▸ haS i₀)
    rw [← hr]; exact dord_alg_nonneg hπ (by rintro rfl; exact ha0 i₀ (by rw [← hr, map_zero]))
  have hu₁ : 1 ≤ dord hπ (a i₁) := by
    obtain ⟨r, hrm, hr⟩ := hs₂R _ (hsc i₁ ▸ haS i₁)
    rw [← hr]; exact one_le_dord_of_max hπ hrm (hr ▸ ha0 i₁)
  have key : ∀ {c : R}, c ∈ maximalIdeal R → ∀ α ∈ g₁, ∀ β ∈ g₂,
      SqEquivMod (fIdeal Q L Ls i₀ i₁) ((1 - algebraMap R F c) ^ 2 + α * β) 1 := by
    intro c hcm α hα β hβ
    rw [hf]
    exact sqEquivMod_sq_add_mul hπ h2 (ha0 i₀) (ha0 i₁) (ha i₀).1 (ha i₁).1 (hgA i₀) (hgA i₁) hu₀ hu₁
      (fun z hz r => mul_sq_mem_normGroup Q hz ⟨r, rfl⟩) hcm hα hβ
  -- the first binary block `y₀, y₁`
  obtain ⟨c₁, hc₁m, hc₁⟩ := hs₂R _ (hYY 0 1)
  have hy01 : bil Q (y 0) (y 1) = 1 - algebraMap R F c₁ := by
    have := hB 0 1; rw [hx01] at this; rw [hc₁]; linear_combination -this
  have hy00 : Q (y 0) = a' - Q (Y 0) := by have := hQ 0; rw [hx00] at this; linear_combination -this
  have hy11 : Q (y 1) = -Q (Y 1) := by have := hQ 1; rw [hx11] at this; linear_combination -this
  have h12 : SqEquivMod (fIdeal Q L Ls i₀ i₁) (bil Q (y 0) (y 1) ^ 2 - Q (y 0) * Q (y 1)) 1 := by
    have := key hc₁m (a' - Q (Y 0)) (sub_mem (hx00 ▸ hxg 0) (hg₂₁ (hQY 0))) (Q (Y 1)) (hQY 1)
    convert this using 1; rw [hy01, hy00, hy11]; ring
  obtain ⟨⟨u₁₂, hu₁₂, hu₁₂'⟩, -⟩ := h12
  rw [mul_one] at hu₁₂'
  obtain ⟨A, hA⟩ := hyR (hy 0) (hy 0)
  obtain ⟨Bv, hBv⟩ := hyR (hy 0) (hy 1)
  obtain ⟨C, hC⟩ := hyR (hy 1) (hy 1)
  rw [bil_self] at hA hC
  have hunit : IsUnit (A * C - Bv ^ 2) := by
    have : A * C - Bv ^ 2 = -u₁₂ := IsFractionRing.injective R F (by
      rw [map_sub, map_mul, map_pow, map_neg, hA, hC, hBv, ← hu₁₂']; ring)
    rw [this]; exact hu₁₂.neg
  -- orthogonalize `y₂`, `y₃` against `y₀`, `y₁`
  have hps : ∀ k l, bil Q (x k) (x l) = 0 → bil Q (y k) (y l) ∈ s₂ := by
    intro k l h
    have := hB k l; rw [h] at this
    have : bil Q (y k) (y l) = -bil Q (Y k) (Y l) := by linear_combination -this
    rw [this]; exact neg_mem (hYY k l)
  obtain ⟨r₀, r₁, hr₀, hr₁, hv₂₀, hv₂₁⟩ := exists_orth_pair Q hA.symm hBv.symm hC.symm hunit
    (hps 2 0 hx20) (hps 2 1 hx21) hs₂R'
  obtain ⟨r₂, r₃, hr₂, hr₃, hv₃₀, hv₃₁⟩ := exists_orth_pair Q hA.symm hBv.symm hC.symm hunit
    (hps 3 0 hx30) (hps 3 1 hx31) hs₂R'
  set w₂ := r₀ • y 0 + r₁ • y 1 with hw₂
  set w₃ := r₂ • y 0 + r₃ • y 1 with hw₃
  set v₂ := y 2 + r₀ • y 0 + r₁ • y 1 with hv₂
  set v₃ := y 3 + r₂ • y 0 + r₃ • y 1 with hv₃
  have hv₂w : v₂ = y 2 + w₂ := by rw [hv₂, hw₂, add_assoc]
  have hv₃w : v₃ = y 3 + w₃ := by rw [hv₃, hw₃, add_assoc]
  have hwK : ∀ {r r' : R}, r • y 0 + r' • y 1 ∈ Ks i₀ := fun {r r'} =>
    add_mem (smul_mem _ r (hy 0)) (smul_mem _ r' (hy 1))
  have hwsub : ∀ {r r' : R}, algebraMap R F r ∈ s₂ → algebraMap R F r' ∈ s₂ →
      r • y 0 + r' • y 1 ∈ subA Q s₂ L := by
    intro r r' hr hr'
    refine ⟨(hK.split.iSup_eq ▸ le_iSup Ks i₀) hwK, fun l hl => ?_⟩
    obtain ⟨b₀, hb₀⟩ := hyL (hy 0) l hl
    obtain ⟨b₁, hb₁⟩ := hyL (hy 1) l hl
    rw [bil_add_left, bil_rsmul_left, bil_rsmul_left, ← hb₀, ← hb₁, mul_comm (algebraMap R F r),
      mul_comm (algebraMap R F r'), ← Algebra.smul_def, ← Algebra.smul_def]
    exact add_mem (smul_mem _ _ hr) (smul_mem _ _ hr')
  have hQv : ∀ {k : Fin 4} {r r' : R}, bil Q (y k + r • y 0 + r' • y 1) (y 0) = 0 →
      bil Q (y k + r • y 0 + r' • y 1) (y 1) = 0 →
      Q (y k + r • y 0 + r' • y 1) = Q (y k) - Q (r • y 0 + r' • y 1) := by
    intro k r r' h0 h1
    have hvw : bil Q (y k + r • y 0 + r' • y 1) (r • y 0 + r' • y 1) = 0 := by
      rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, h0, h1]; ring
    have e1 : y k + r • y 0 + r' • y 1 = y k + (r • y 0 + r' • y 1) := by rw [add_assoc]
    rw [e1] at hvw ⊢
    rw [bil_add_left, bil_self] at hvw
    rw [Q_add]; linear_combination 2 * hvw
  have hQv₂ : Q v₂ = a'' - (Q (Y 2) + Q w₂) := by
    rw [hQv hv₂₀ hv₂₁]; have := hQ 2; rw [hx22] at this; linear_combination -this
  have hQv₃ : Q v₃ = -(Q (Y 3) + Q w₃) := by
    rw [hQv hv₃₀ hv₃₁]; have := hQ 3; rw [hx33] at this; linear_combination -this
  have hQw₂ : Q w₂ ∈ g₂ := hg₂ ▸ Q_mem_normGroup Q (hwsub hr₀ hr₁)
  have hQw₃ : Q w₃ ∈ g₂ := hg₂ ▸ Q_mem_normGroup Q (hwsub hr₂ hr₃)
  have hv₂w₃ : bil Q v₂ w₃ = 0 := by
    rw [hw₃, bil_add_right, bil_rsmul_right, bil_rsmul_right, hv₂₀, hv₂₁]; ring
  have hB₂₃ : bil Q v₂ v₃ = 1 - (bil Q (Y 2) (Y 3) - algebraMap R F r₀ * bil Q (y 0) (y 3) -
      algebraMap R F r₁ * bil Q (y 1) (y 3)) := by
    rw [hv₃w, bil_add_right, hv₂w₃, add_zero, hv₂, bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left]
    have := hB 2 3; rw [hx23] at this; linear_combination -this
  have hc₂s : bil Q (Y 2) (Y 3) - algebraMap R F r₀ * bil Q (y 0) (y 3) -
      algebraMap R F r₁ * bil Q (y 1) (y 3) ∈ s₂ := by
    obtain ⟨b₀, hb₀⟩ := hyR (hy 0) (hy 3)
    obtain ⟨b₁, hb₁⟩ := hyR (hy 1) (hy 3)
    rw [← hb₀, ← hb₁, mul_comm (algebraMap R F r₀), mul_comm (algebraMap R F r₁), ← Algebra.smul_def,
      ← Algebra.smul_def]
    exact sub_mem (sub_mem (hYY 2 3) (smul_mem _ _ hr₀)) (smul_mem _ _ hr₁)
  obtain ⟨c₂, hc₂m, hc₂⟩ := hs₂R _ hc₂s
  have h34 : SqEquivMod (fIdeal Q L Ls i₀ i₁) (bil Q v₂ v₃ ^ 2 - Q v₂ * Q v₃) 1 := by
    have := key hc₂m (a'' - (Q (Y 2) + Q w₂)) (sub_mem (hx22 ▸ hxg 2) (hg₂₁ (add_mem (hQY 2) hQw₂)))
      (Q (Y 3) + Q w₃) (add_mem (hQY 3) hQw₃)
    convert this using 1; rw [hB₂₃, hQv₂, hQv₃, hc₂]; ring
  have h12' : SqEquivMod (fIdeal Q L Ls i₀ i₁) (bil Q (y 0) (y 1) ^ 2 - Q (y 0) * Q (y 1)) 1 := by
    have := key hc₁m (a' - Q (Y 0)) (sub_mem (hx00 ▸ hxg 0) (hg₂₁ (hQY 0))) (Q (Y 1)) (hQY 1)
    convert this using 1; rw [hy01, hy00, hy11]; ring
  have hv₂K : v₂ ∈ Ks i₀ := add_mem (add_mem (hy 2) (smul_mem _ _ (hy 0))) (smul_mem _ _ (hy 1))
  have hv₃K : v₃ ∈ Ks i₀ := add_mem (add_mem (hy 3) (smul_mem _ _ (hy 0))) (smul_mem _ _ (hy 1))
  have hv₂y0 : bil Q (y 0) v₂ = 0 := by rw [bil_comm]; exact hv₂₀
  have hv₂y1 : bil Q (y 1) v₂ = 0 := by rw [bil_comm]; exact hv₂₁
  have hv₃y0 : bil Q (y 0) v₃ = 0 := by rw [bil_comm]; exact hv₃₀
  have hv₃y1 : bil Q (y 1) v₃ = 0 := by rw [bil_comm]; exact hv₃₁
  -- the weight generator `w` of `L^{s₁}` and the data of `hlt`
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have hfsub_sc : scale Q (fundSub Q L Ls i₀) = 1 := by rw [scale_fundSub Q hfg hL i₀, hU]
  have hwbd := weight_bounds Q (fundSub Q L Ls i₀)
  have hwle1 : fundWeight Q L Ls i₀ ≤ 1 :=
    hwbd.2.2.2.trans ((normIdeal_le_scale Q _).trans hfsub_sc.le)
  have h2w : (2 : F) ∈ fundWeight Q L Ls i₀ := by
    have h1 : (1 : F) ∈ scale Q (fundSub Q L Ls i₀) := by
      rw [hfsub_sc]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    have := hwbd.2.2.1 (Submodule.smul_mem_pointwise_smul (1 : F) (2 : F) _ h1)
    have h2' : (2 : F) ∈ weight Q (fundSub Q L Ls i₀) := by simpa using this
    exact h2'
  have hwfg : (fundWeight Q L Ls i₀).FG :=
    FG.of_le (Submodule.fg_span_singleton (a i₀)) (hwbd.2.2.2.trans (le_of_eq (ha i₀).2.symm))
  have hwne : fundWeight Q L Ls i₀ ≠ ⊥ := fun h => h2F (by simpa [h] using h2w)
  obtain ⟨w, hw0, hwdef⟩ := exists_eq_span_singleton (R := R) hwfg hwne
  have hw1 : ∃ r : R, algebraMap R F r = w :=
    Submodule.mem_one.1 (hwle1 (hwdef ▸ mem_span_singleton_self w))
  have hw2 : ∃ r : R, algebraMap R F r * w = 2 := by
    obtain ⟨r, hr⟩ := mem_span_singleton.1 (hwdef ▸ h2w)
    exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  have ha0R : ∃ r : R, algebraMap R F r = a i₀ := Submodule.mem_one.1 (hU ▸ haS i₀)
  have hlt' : fIdeal Q L Ls i₀ i₁ < R ∙ (4 * a i₀ * w⁻¹) := by
    rw [hwdef, smul_one_div_span hw0] at hlt; exact hlt
  have hle : R ∙ a i₁ ≤ R ∙ a i₀ :=
    (span_singleton_le_iff_mem _ _).2 (hgA i₀ _ (hg₂₁ (ha i₁).1))
  rcases hle.lt_or_eq with hlt₁ | heq
  swap
  · -- the case `u₁ = u₂`: condition (iii) is vacuous
    exfalso
    have hdord : dord hπ (a i₁) = dord hπ (a i₀) :=
      (FIdealAux.span_eq_iff_dord hπ (ha0 i₁) (ha0 i₀)).1 heq
    have hm := mul_fIdeal_of_dord_eq Q hπ h2p hfg hreg hL ha i₀ i₁ (by omega) (σ := 1)
      (by rw [hU, Submodule.one_eq_span]) hdord
    rw [hU, Submodule.one_mul, Submodule.one_mul] at hm
    rw [hm, hwdef, FundAux.smul_eq_span_mul, FIdealAux.span_mul_span'] at hlt'
    obtain ⟨v, hv⟩ := mem_span_singleton.1 (heq ▸ mem_span_singleton_self (a i₀) : a i₀ ∈ R ∙ a i₁)
    have hv' : a i₀ = algebraMap R F v * a i₁ := by rw [← hv, Algebra.smul_def]
    obtain ⟨tr, htr⟩ := hw2
    refine hlt'.not_ge ((span_singleton_le_iff_mem _ _).2 (mem_span_singleton.2 ⟨v * tr * tr, ?_⟩))
    rw [Algebra.smul_def, hv']
    simp only [map_mul]
    field_simp
    linear_combination (algebraMap R F v * a i₁ * (algebraMap R F tr * w + 2)) * htr
  -- the case `u₁ < u₂`
  have hρa : ∀ z ∈ g₂, ∃ ρ ∈ maximalIdeal R, z = algebraMap R F ρ * a i₀ := fun z hz =>
    mem_p_mul_of_lt hlt₁ (hgA i₁ z hz)
  have hAα : ∀ z ∈ g₁, ∃ α b : R, z = a i₀ * algebraMap R F α ^ 2 + w * algebraMap R F b := by
    intro z hz
    obtain ⟨ε, hε⟩ := exists_sub_sq_mem_weight Q h2p (ha i₀) (ha0 i₀) hz
    have hε' : z - a i₀ * algebraMap R F ε ^ 2 ∈ R ∙ w := by rw [← hwdef]; exact hε
    obtain ⟨b, hb⟩ := mem_span_singleton.1 hε'
    exact ⟨ε, b, by rw [Algebra.smul_def] at hb; linear_combination -hb⟩
  have hf' : ∀ x ∈ fIdeal Q L Ls i₀ i₁, ∃ ρ ∈ maximalIdeal R,
      x = algebraMap R F ρ * (4 * a i₀ / w) := by
    intro x hx
    obtain ⟨ρ, hρ, hxρ⟩ := mem_p_mul_of_lt hlt' hx
    exact ⟨ρ, hρ, by rw [hxρ]; ring⟩
  -- unit multiples of `a₀`
  have hunitmul : ∀ {a₃ : F}, IsNormGenerator Q (fundSub Q L Ls i₀) a₃ → ∀ z ∈ g₂,
      ∃ u : R, IsUnit u ∧ a₃ - z = a i₀ * algebraMap R F u := by
    intro a₃ ha₃ z hz
    obtain ⟨ub, hub⟩ := span_singleton_eq_span_singleton.mp (ha₃.2.trans (ha i₀).2.symm)
    have hb : a₃ = algebraMap R F ((ub⁻¹ : Rˣ) : R) * a i₀ := by
      have : a₃ = ((ub⁻¹ : Rˣ) : R) • a i₀ := by rw [← hub, Units.smul_def, smul_smul]; simp
      rw [this, Algebra.smul_def]
    obtain ⟨ρ, hρ, hzρ⟩ := hρa z hz
    refine ⟨((ub⁻¹ : Rˣ) : R) + -ρ, isUnit_add_mem' (ub⁻¹).isUnit ((Ideal.neg_mem_iff _).2 hρ), ?_⟩
    rw [hb, hzρ]; simp only [map_add, map_neg]; ring
  -- the quadratic space `FK₁ ⊥ ⟨a₀⟩`
  have hQW : ∀ u : V, repForm Q (a i₀) (u, 0) = Q u := fun u => by simp [repForm_apply]
  have hbW : ∀ u v : V, bil (repForm Q (a i₀)) (u, 0) (v, 0) = bil Q u v := fun u v => by
    simp [bil_repForm]
  have hbE : ∀ u : V, bil (repForm Q (a i₀)) (u, 0) ((0 : V), (1 : F)) = 0 := fun u => by
    simp [bil_repForm]
  have hQE : repForm Q (a i₀) ((0 : V), (1 : F)) = a i₀ := by simp [repForm_apply]
  have hδ' : ∀ {p q : V}, SqEquivMod (fIdeal Q L Ls i₀ i₁) (bil Q p q ^ 2 - Q p * Q q) 1 →
      ∃ ε : R, IsUnit ε ∧ ∃ x ∈ fIdeal Q L Ls i₀ i₁,
        bil (repForm Q (a i₀)) (p, 0) (q, 0) ^ 2 - repForm Q (a i₀) (p, 0) * repForm Q (a i₀) (q, 0) =
          algebraMap R F ε ^ 2 + x := by
    intro p q h
    obtain ⟨-, ε, hε, hmem⟩ := h
    exact ⟨ε, hε, _, hmem, by rw [hbW, hQW, hQW]; ring⟩
  -- round 1: `y₀, y₁, e`
  have hA₁ : ∃ u : R, IsUnit u ∧ repForm Q (a i₀) (y 0, 0) = a i₀ * algebraMap R F u := by
    obtain ⟨u, hu, hue⟩ := hunitmul ha' (Q (Y 0)) (hQY 0)
    exact ⟨u, hu, by rw [hQW, hy00]; exact hue⟩
  have hAα₁ : ∃ α b : R, repForm Q (a i₀) (y 0, 0) =
      a i₀ * algebraMap R F α ^ 2 + w * algebraMap R F b := by
    have : Q (y 0) ∈ g₁ := by rw [hy00]; exact sub_mem ha'.1 (hg₂₁ (hQY 0))
    obtain ⟨α, b, h⟩ := hAα _ this
    exact ⟨α, b, by rw [hQW]; exact h⟩
  obtain ⟨r₁, r₂, z₁, hS1, hr₁Q, hr₂Q, hr₁₂, hr₁z, hr₂z, b₁', hz₁Q⟩ :=
    round_step (repForm Q (a i₀)) h2p (ha0 i₀) hw0 ha0R hw1 hw2 hf' hA₁ hAα₁ (hδ' h12')
      (hbE _) (hbE _) ⟨0, by rw [hQE]; simp⟩
  -- the vectors of `J'` are orthogonal to `J ⊥ ⟨e⟩`
  set QW := repForm Q (a i₀) with hQWdef
  let SV : Submodule F (V × F) :=
    LinearMap.ker (QuadraticMap.associated QW ((v₂ : V), (0 : F))) ⊓
      LinearMap.ker (QuadraticMap.associated QW ((v₃ : V), (0 : F)))
  have hmemSV : ∀ p : V × F, p ∈ SV ↔ bil QW ((v₂ : V), (0 : F)) p = 0 ∧ bil QW ((v₃ : V), (0 : F)) p = 0 :=
    fun p => by simp [SV, LinearMap.mem_ker, bil]
  have hy0SV : (y 0, (0 : F)) ∈ SV := (hmemSV _).2 ⟨by rw [hbW, bil_comm]; exact hv₂y0,
    by rw [hbW, bil_comm]; exact hv₃y0⟩
  have hy1SV : (y 1, (0 : F)) ∈ SV := (hmemSV _).2 ⟨by rw [hbW, bil_comm]; exact hv₂y1,
    by rw [hbW, bil_comm]; exact hv₃y1⟩
  have heSV : ((0 : V), (1 : F)) ∈ SV := (hmemSV _).2 ⟨hbE _, hbE _⟩
  obtain ⟨hr₁SV, hr₂SV, hz₁SV⟩ := hS1 SV hy0SV hy1SV heSV
  obtain ⟨hz₀₂, hz₁₂⟩ := (hmemSV _).1 hz₁SV
  obtain ⟨hr₁₂a, hr₁₂b⟩ := (hmemSV _).1 hr₁SV
  obtain ⟨hr₂₂a, hr₂₂b⟩ := (hmemSV _).1 hr₂SV
  -- round 2: `v₂, v₃, z₁`
  have hA₂ : ∃ u : R, IsUnit u ∧ repForm Q (a i₀) (v₂, 0) = a i₀ * algebraMap R F u := by
    obtain ⟨u, hu, hue⟩ := hunitmul ha'' (Q (Y 2) + Q w₂) (add_mem (hQY 2) hQw₂)
    exact ⟨u, hu, by rw [hQW, hQv₂]; linear_combination hue⟩
  have hAα₂ : ∃ α b : R, repForm Q (a i₀) (v₂, 0) =
      a i₀ * algebraMap R F α ^ 2 + w * algebraMap R F b := by
    have : Q v₂ ∈ g₁ := by
      rw [hQv₂]; exact sub_mem ha''.1 (hg₂₁ (add_mem (hQY 2) hQw₂))
    obtain ⟨α, b, h⟩ := hAα _ this
    exact ⟨α, b, by rw [hQW]; exact h⟩
  obtain ⟨r₃, r₄, z₂, hS2, hr₃Q, hr₄Q, hr₃₄, hr₃z, hr₄z, b₂', hz₂Q⟩ :=
    round_step QW h2p (ha0 i₀) hw0 ha0R hw1 hw2 hf' hA₂ hAα₂ (hδ' h34) hz₀₂ hz₁₂ ⟨b₁', hz₁Q⟩
  -- orthogonality of the two hyperbolic pairs
  let SR : Submodule F (V × F) :=
    LinearMap.ker (QuadraticMap.associated QW r₁) ⊓ LinearMap.ker (QuadraticMap.associated QW r₂)
  have hmemSR : ∀ p : V × F, p ∈ SR ↔ bil QW r₁ p = 0 ∧ bil QW r₂ p = 0 :=
    fun p => by simp [SR, LinearMap.mem_ker, bil]
  have hv₂SR : ((v₂ : V), (0 : F)) ∈ SR := (hmemSR _).2 ⟨by rw [bil_comm]; exact hr₁₂a,
    by rw [bil_comm]; exact hr₂₂a⟩
  have hv₃SR : ((v₃ : V), (0 : F)) ∈ SR := (hmemSR _).2 ⟨by rw [bil_comm]; exact hr₁₂b,
    by rw [bil_comm]; exact hr₂₂b⟩
  have hz₁SR : z₁ ∈ SR := (hmemSR _).2 ⟨hr₁z, hr₂z⟩
  obtain ⟨hr₃SR, hr₄SR, -⟩ := hS2 SR hv₂SR hv₃SR hz₁SR
  obtain ⟨h13, h23⟩ := (hmemSR _).1 hr₃SR
  obtain ⟨h14, h24⟩ := (hmemSR _).1 hr₄SR
  -- the first components lie in `FK₁`
  let SK : Submodule F (V × F) := (span F (Ks i₀ : Set V)).prod ⊤
  have hSK : ∀ {u : V}, u ∈ Ks i₀ → (u, (0 : F)) ∈ SK := fun hu =>
    ⟨subset_span hu, trivial⟩
  have heSK : ((0 : V), (1 : F)) ∈ SK := ⟨zero_mem _, trivial⟩
  obtain ⟨hr₁SK, hr₂SK, hz₁SK⟩ := hS1 SK (hSK (hy 0)) (hSK (hy 1)) heSK
  obtain ⟨hr₃SK, hr₄SK, -⟩ := hS2 SK (hSK hv₂K) (hSK hv₃K) hz₁SK
  -- the frame: two orthogonal hyperbolic planes carrying the base of `L₁`
  have hr₂₁ : bil QW r₂ r₁ = 1 := by rw [bil_comm]; exact hr₁₂
  have hr₄₃ : bil QW r₄ r₃ = 1 := by rw [bil_comm]; exact hr₃₄
  have h31 : bil QW r₃ r₁ = 0 := by rw [bil_comm]; exact h13
  have h32 : bil QW r₃ r₂ = 0 := by rw [bil_comm]; exact h23
  have h41 : bil QW r₄ r₁ = 0 := by rw [bil_comm]; exact h14
  have h42 : bil QW r₄ r₂ = 0 := by rw [bil_comm]; exact h24
  set X : Fin 4 → V × F := ![r₂ + (a' / 2) • r₁, r₁, r₄ + (a'' / 2) • r₃, r₃] with hXdef
  have hGX : ∀ k l, bil QW (X k) (X l) = blk2 a' 0 a'' 0 k l := by
    intro k l
    fin_cases k <;> fin_cases l <;>
      simp [hXdef, blk2, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, bil_self, Q_add, Q_smul, hr₁Q, hr₂Q,
        hr₃Q, hr₄Q, hr₁₂, hr₂₁, hr₃₄, hr₄₃, h13, h31, h23, h32, h14, h41, h24, h42] <;> ring
  have hXK : ∀ k, (X k).1 ∈ span F (Ks i₀ : Set V) := by
    intro k
    have hX : X k ∈ SK := by
      fin_cases k
      · exact add_mem hr₂SK (smul_mem _ _ hr₁SK)
      · exact hr₁SK
      · exact add_mem hr₄SK (smul_mem _ _ hr₃SK)
      · exact hr₃SK
    exact hX.1
  refine spanRepresents_of_frame Q (a i₀) e X hXK (fun k l => ?_) ?_
  · rw [he, ← bil_repForm, hGX]
  · rw [he, det_blk2]; simp

end Main

end QuadFormsKB.OMeara.NecBase
