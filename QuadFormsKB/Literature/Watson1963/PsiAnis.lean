/-
# Watson (1963): the scaled binary $2A$ inside the even-Hessian part

For $\psi$ over $\mathbb Z_2$ with all Hessian entries even and square-free at $2$ (`SqFreePsi`), in at least $4$
variables, there are $x, y$ with $\psi(x) \equiv \psi(y) \equiv 2$ and $x^{\mathsf T}H_\psi y \equiv 2 \pmod 4$
(`psi_exists_anisotropic_pair`): their span is $2B$ with $B$ an even unimodular binary of the type of
$A = x^2 + xy + y^2$. *Proof:* reduce modulo $2$: on $W = \{\bar v : \psi(v) \text{ even}\} \subseteq \mathbb F_2^m$
(dimension $\ge m - 1 \ge 3$), $q = \psi/2$ and $b = x^{\mathsf T}H_\psi y/2$ modulo $2$ are well defined (the Hessian
is even, so $\psi$ and the pairing are well defined modulo $4$ on classes modulo $2$), `SqFreePsi` says the radical of
$q$ on $W$ is trivial, and `exists_aniso_pair` applies.
-/
import QuadFormsKB.Literature.Watson1963.PsiValues
import QuadFormsKB.Literature.Watson1963.F2Aniso

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {m : ℕ}

/-- The lift $\mathbb F_2^m \to \mathbb Z_2^m$ by the representatives $0, 1$. -/
def liftV (v : Fin m → ZMod 2) : Fin m → ℤ_[2] := fun i => ((v i).val : ℤ_[2])

theorem liftV_red (v : Fin m → ZMod 2) (i : Fin m) : PadicInt.toZMod (liftV v i) = v i := toZMod_lift (v i)

theorem two_dvd_sub_of_toZMod_eq {a b : ℤ_[2]} (h : PadicInt.toZMod a = PadicInt.toZMod b) :
    (2 : ℤ_[2]) ∣ a - b := two_dvd_of_toZMod' (by rw [map_sub, h, sub_self])

theorem toZMod_eq_of_four_dvd {a b : ℤ_[2]} (h : (4 : ℤ_[2]) ∣ 2 * a - 2 * b) :
    PadicInt.toZMod a = PadicInt.toZMod b := by
  obtain ⟨c, hc⟩ := h
  have h2 : (2 : ℤ_[2]) * (a - b - 2 * c) = 0 := by linear_combination hc
  have := (mul_eq_zero.1 h2).resolve_left (by norm_num)
  rw [← sub_eq_zero, ← map_sub, show a - b = 2 * c by linear_combination this]
  exact toZMod_eq_zero_of_two_dvd (dvd_mul_right 2 c)

theorem liftV_add (v w : Fin m → ZMod 2) (i : Fin m) :
    (2 : ℤ_[2]) ∣ liftV (v + w) i - (liftV v + liftV w) i :=
  two_dvd_sub_of_toZMod_eq (by simp only [Pi.add_apply, map_add, liftV_red])

theorem liftV_zero : liftV (0 : Fin m → ZMod 2) = 0 := funext fun i => by simp [liftV]

theorem liftV_red_self (x : Fin m → ℤ_[2]) (i : Fin m) :
    (2 : ℤ_[2]) ∣ liftV (fun j => PadicInt.toZMod (x j)) i - x i :=
  two_dvd_sub_of_toZMod_eq (by rw [liftV_red])

theorem refl_two (x : Fin m → ℤ_[2]) : ∀ i, (2 : ℤ_[2]) ∣ x i - x i := fun i => by simp

section Psi

variable (ψ : QuadForm ℤ_[2] m) (hpsi : ∀ i j, (2 : ℤ_[2]) ∣ ψ.hessian i j)
include hpsi

theorem dot_even (x y : Fin m → ℤ_[2]) : (2 : ℤ_[2]) ∣ x ⬝ᵥ (ψ.hessian *ᵥ y) := by
  simp only [dotProduct, mulVec]
  exact Finset.dvd_sum fun a _ => Dvd.dvd.mul_left (Finset.dvd_sum fun b _ => Dvd.dvd.mul_right (hpsi a b) _) _

/-- Values modulo $4$ only depend on the class modulo $2$. -/
theorem eval_congr_four {x x' : Fin m → ℤ_[2]} (h : ∀ i, (2 : ℤ_[2]) ∣ x i - x' i) :
    (4 : ℤ_[2]) ∣ ψ.eval x - ψ.eval x' := by
  choose t ht using h
  have hx : x = x' + (2 : ℤ_[2]) • t := funext fun i => by simp [← ht i]
  rw [hx]
  have hp := QuadForm.eval_polar ψ x' ((2 : ℤ_[2]) • t)
  rw [eval_smul_sq, mulVec_smul, dotProduct_smul, smul_eq_mul] at hp
  obtain ⟨c, hc⟩ := dot_even ψ hpsi x' t
  exact ⟨ψ.eval t + c, by linear_combination hp + 2 * hc⟩

theorem dot_congr_four {x x' : Fin m → ℤ_[2]} (h : ∀ i, (2 : ℤ_[2]) ∣ x i - x' i) (y : Fin m → ℤ_[2]) :
    (4 : ℤ_[2]) ∣ x ⬝ᵥ (ψ.hessian *ᵥ y) - x' ⬝ᵥ (ψ.hessian *ᵥ y) := by
  choose t ht using h
  have hx : x = x' + (2 : ℤ_[2]) • t := funext fun i => by simp [← ht i]
  rw [hx, add_dotProduct, smul_dotProduct, smul_eq_mul]
  obtain ⟨c, hc⟩ := dot_even ψ hpsi t y
  exact ⟨c, by linear_combination 2 * hc⟩

/-- The mod-2 functional $\bar v \mapsto \psi(v) \bmod 2$. -/
def ellψ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := PadicInt.toZMod (ψ.eval (liftV v))
  map_add' v w := by
    have h1 := eval_congr_four ψ hpsi (liftV_add v w)
    have h2 := psi_eval_add ψ (liftV v) (liftV w)
    obtain ⟨c, hc⟩ := dot_even ψ hpsi (liftV v) (liftV w)
    have : PadicInt.toZMod (ψ.eval (liftV (v + w))) = PadicInt.toZMod (ψ.eval (liftV v) + ψ.eval (liftV w)) := by
      rw [← sub_eq_zero, ← map_sub]
      apply toZMod_eq_zero_of_two_dvd
      obtain ⟨d, hd⟩ := h1
      exact ⟨2 * d + c, by linear_combination hd + h2 + hc⟩
    rw [this, map_add]
  map_smul' c v := by
    rcases zmod2_cases c with rfl | rfl
    · simp [liftV_zero, eval_zero_vec]
    · simp

/-- The polar form modulo $2$ of $\psi/2$: $b(\bar v, \bar w) = (v^{\mathsf T}H_\psi w)/2 \bmod 2$. -/
def bψ (v w : Fin m → ZMod 2) : ZMod 2 :=
  PadicInt.toZMod (Classical.choose (dot_even ψ hpsi (liftV v) (liftV w)))

theorem bψ_spec {v w : Fin m → ZMod 2} {x y : Fin m → ℤ_[2]} (hx : ∀ i, (2 : ℤ_[2]) ∣ x i - liftV v i)
    (hy : ∀ i, (2 : ℤ_[2]) ∣ y i - liftV w i) {g : ℤ_[2]} (hg : x ⬝ᵥ (ψ.hessian *ᵥ y) = 2 * g) :
    PadicInt.toZMod g = bψ ψ hpsi v w := by
  have hs := Classical.choose_spec (dot_even ψ hpsi (liftV v) (liftV w))
  unfold bψ
  apply toZMod_eq_of_four_dvd
  rw [← hg, ← hs]
  have h1 := dot_congr_four ψ hpsi hx y
  have h2 := dot_congr_four ψ hpsi hy (liftV v)
  rw [dot_symm ψ y, dot_symm ψ (liftV w)] at h2
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- The quadratic form $q(\bar v) = \psi(v)/2 \bmod 2$ (meaningful where $\psi(v)$ is even). -/
def qψ (v : Fin m → ZMod 2) : ZMod 2 :=
  haveI := Classical.dec ((2 : ℤ_[2]) ∣ ψ.eval (liftV v))
  if h : (2 : ℤ_[2]) ∣ ψ.eval (liftV v) then PadicInt.toZMod (Classical.choose h) else 0

theorem qψ_spec {v : Fin m → ZMod 2} {x : Fin m → ℤ_[2]} (hx : ∀ i, (2 : ℤ_[2]) ∣ x i - liftV v i)
    {a : ℤ_[2]} (ha : ψ.eval x = 2 * a) : PadicInt.toZMod a = qψ ψ v := by
  have h4 := eval_congr_four ψ hpsi hx
  have hev : (2 : ℤ_[2]) ∣ ψ.eval (liftV v) := by
    obtain ⟨c, hc⟩ := h4
    exact ⟨a - 2 * c, by linear_combination -hc + ha⟩
  unfold qψ
  rw [dif_pos hev]
  apply toZMod_eq_of_four_dvd
  rw [← ha, ← Classical.choose_spec hev]
  exact h4

theorem even_of_mem_ker {v : Fin m → ZMod 2} (hv : ellψ ψ hpsi v = 0) : (2 : ℤ_[2]) ∣ ψ.eval (liftV v) :=
  two_dvd_of_toZMod' hv

/-- **(ψ3)** see the module docstring. -/
theorem psi_exists_anisotropic_pair (hSF : SqFreePsi ψ) (hm : 4 ≤ m) :
    ∃ x y : Fin m → ℤ_[2], (∃ a, ψ.eval x = 2 * a ∧ ¬ (2 : ℤ_[2]) ∣ a) ∧
      (∃ a, ψ.eval y = 2 * a ∧ ¬ (2 : ℤ_[2]) ∣ a) ∧ (∃ b, x ⬝ᵥ (ψ.hessian *ᵥ y) = 2 * b ∧ ¬ (2 : ℤ_[2]) ∣ b) := by
  classical
  set W := LinearMap.ker (ellψ ψ hpsi)
  have hsum : ∀ v w : Fin m → ZMod 2, ∀ i, (2 : ℤ_[2]) ∣ (liftV v + liftV w) i - liftV (v + w) i := by
    intro v w i
    have := liftV_add v w i
    rw [← neg_sub]; exact (dvd_neg).2 this
  have hb_add : ∀ v v' w, bψ ψ hpsi (v + v') w = bψ ψ hpsi v w + bψ ψ hpsi v' w := by
    intro v v' w
    obtain ⟨g, hg⟩ := dot_even ψ hpsi (liftV v) (liftV w)
    obtain ⟨g', hg'⟩ := dot_even ψ hpsi (liftV v') (liftV w)
    rw [← bψ_spec ψ hpsi (refl_two _) (refl_two _) hg, ← bψ_spec ψ hpsi (refl_two _) (refl_two _) hg', ← map_add]
    exact (bψ_spec ψ hpsi (hsum v v') (refl_two _) (g := g + g') (by rw [add_dotProduct, hg, hg']; ring)).symm
  have hb_smul : ∀ (c : ZMod 2) v w, bψ ψ hpsi (c • v) w = c * bψ ψ hpsi v w := by
    intro c v w
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, zero_mul]
      have := bψ_spec ψ hpsi (v := 0) (w := w) (x := 0) (y := liftV w) (fun i => by simp [liftV_zero])
        (refl_two _) (g := 0) (by simp)
      rw [← this, map_zero]
    · rw [one_smul, one_mul]
  have hb_symm : ∀ v w, bψ ψ hpsi v w = bψ ψ hpsi w v := by
    intro v w
    obtain ⟨g, hg⟩ := dot_even ψ hpsi (liftV v) (liftV w)
    rw [← bψ_spec ψ hpsi (refl_two _) (refl_two _) hg]
    exact bψ_spec ψ hpsi (refl_two _) (refl_two _) (by rw [dot_symm ψ, hg])
  have hq : ∀ v ∈ W, ∀ w ∈ W, qψ ψ (v + w) = qψ ψ v + qψ ψ w + bψ ψ hpsi v w := by
    intro v hv w hw
    obtain ⟨a, ha⟩ := even_of_mem_ker ψ hpsi hv
    obtain ⟨a', ha'⟩ := even_of_mem_ker ψ hpsi hw
    obtain ⟨g, hg⟩ := dot_even ψ hpsi (liftV v) (liftV w)
    rw [← qψ_spec ψ hpsi (refl_two _) ha, ← qψ_spec ψ hpsi (refl_two _) ha',
      ← bψ_spec ψ hpsi (refl_two _) (refl_two _) hg, ← map_add, ← map_add]
    exact (qψ_spec ψ hpsi (hsum v w) (a := a + a' + g) (by rw [psi_eval_add, ha, ha', hg]; ring)).symm
  have hrad : ∀ v ∈ W, qψ ψ v = 0 → (∀ w ∈ W, bψ ψ hpsi v w = 0) → v = 0 := by
    intro v hv hq0 hb0
    obtain ⟨a, ha⟩ := even_of_mem_ker ψ hpsi hv
    have ha0 : PadicInt.toZMod a = 0 := by rw [qψ_spec ψ hpsi (refl_two _) ha]; exact hq0
    have h4 : (4 : ℤ_[2]) ∣ ψ.eval (liftV v) := by
      obtain ⟨c, hc⟩ := two_dvd_of_toZMod' ha0
      exact ⟨c, by rw [ha, hc]; ring⟩
    have hz : ∀ c', (2 : ℤ_[2]) ∣ ψ.eval c' → (4 : ℤ_[2]) ∣ c' ⬝ᵥ (ψ.hessian *ᵥ liftV v) := by
      intro c' hc'
      set w : Fin m → ZMod 2 := fun j => PadicInt.toZMod (c' j)
      have hcw : ∀ i, (2 : ℤ_[2]) ∣ c' i - liftV w i := fun i => by
        rw [← neg_sub]; exact (dvd_neg).2 (liftV_red_self c' i)
      have hwW : w ∈ W := by
        show PadicInt.toZMod (ψ.eval (liftV w)) = 0
        apply toZMod_eq_zero_of_two_dvd
        have := eval_congr_four ψ hpsi hcw
        exact (dvd_sub_right hc').1 (dvd_trans ⟨2, by norm_num⟩ this)
      obtain ⟨g, hg⟩ := dot_even ψ hpsi c' (liftV v)
      have hbg := bψ_spec ψ hpsi (v := w) (w := v) hcw (refl_two _) hg
      rw [hb_symm, hb0 w hwW] at hbg
      obtain ⟨d, hd⟩ := two_dvd_of_toZMod' hbg
      exact ⟨d, by rw [hg, hd]; ring⟩
    have h2 := hSF (liftV v) h4 hz
    funext i
    rw [← liftV_red v i]
    exact toZMod_eq_zero_of_two_dvd (h2 i)
  have hdim : 3 ≤ Module.finrank (ZMod 2) W := by
    have e1 := LinearMap.finrank_range_add_finrank_ker (ellψ ψ hpsi)
    have e2 : Module.finrank (ZMod 2) (LinearMap.range (ellψ ψ hpsi)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (ellψ ψ hpsi)); simpa using this
    simp only [Module.finrank_fin_fun] at e1
    show 3 ≤ Module.finrank (ZMod 2) (LinearMap.ker (ellψ ψ hpsi))
    omega
  obtain ⟨v, hv, w, hw, hqv, hqw, hbvw⟩ :=
    exists_aniso_pair W (qψ ψ) (bψ ψ hpsi) hb_add hb_smul hb_symm hq hrad hdim
  obtain ⟨a, ha⟩ := even_of_mem_ker ψ hpsi hv
  obtain ⟨a', ha'⟩ := even_of_mem_ker ψ hpsi hw
  obtain ⟨g, hg⟩ := dot_even ψ hpsi (liftV v) (liftV w)
  have hodd : ∀ t : ℤ_[2], PadicInt.toZMod t = 1 → ¬ (2 : ℤ_[2]) ∣ t := fun t ht h2 => by
    rw [toZMod_eq_zero_of_two_dvd h2] at ht; exact absurd ht (by decide)
  refine ⟨liftV v, liftV w, ⟨a, ha, hodd a ?_⟩, ⟨a', ha', hodd a' ?_⟩, ⟨g, hg, hodd g ?_⟩⟩
  · rw [qψ_spec ψ hpsi (refl_two _) ha]; exact hqv
  · rw [qψ_spec ψ hpsi (refl_two _) ha']; exact hqw
  · rw [bψ_spec ψ hpsi (refl_two _) (refl_two _) hg]; exact hbvw

end Psi

end QuadFormsKB.Watson1963
