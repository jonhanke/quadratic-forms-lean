/-
# Watson (1963), §2: minimal forms are square-free at $2$

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), §2, proof of
Theorem 2, p. 551 (with Watson 1962, Theorems 3, 4). Let $f$ be a Watson-minimal positive definite form,
$\Lambda = \Lambda_2(f)$ Watson's sublattice (`watsonSub f 2`: the $y$ with $2 \mid f(y)$ and
$H_f y \equiv 0 \pmod 2$) and $g$ the derived form, $f(B\vec x) = 2g(\vec x)$ for a basis matrix $B$ of $\Lambda$.
Minimality gives $n \le r_2(f) + r_2(g)$ (`IsWatsonMinimal.exists_derived_rank_ge`); always $2\mathbb Z^n$ lies in
$\Lambda_2(g)$ (pulled back by $B$), and this is the whole of $\Lambda_2(g)$ exactly when $r_2(f) + r_2(g) = n$.
Concretely (`IsWatsonMinimal.sqFree_int`): **if $y \in \Lambda$, $4 \mid f(y)$ and $z^{\mathsf T} H_f y \equiv 0
\pmod 4$ for all $z \in \Lambda$, then $y \equiv 0 \pmod 2$.** This is Watson's condition that both parts $f_1$ and
$f_2$ of his normal form (2.5) have odd discriminant (2.6), at $p = 2$.

The condition only involves $f$ modulo $4$, so it passes to $\mathbb Z_2$ (`SqFree2`, `IsWatsonMinimal.sqFree2`) and is
invariant under $\mathbb Z_2$-isometry (`SqFree2.of_isometricGL`).
-/
import QuadFormsKB.Literature.Watson1963.ProbesOdd
import QuadFormsKB.Literature.Watson1963.TwoAdicSplit

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n : ℕ}

/-- Helper: $Q(c\vec x) = c^2 Q(\vec x)$ over any commutative ring. -/
theorem eval_smul_sq {R : Type*} [CommRing R] (Q : QuadForm R n) (c : R) (x : Fin n → R) :
    Q.eval (c • x) = c ^ 2 * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp; ring

/-! ### Integer facts -/

/-- Helper: an element of $\Lambda_p$ pairs to a multiple of $p$ with every vector. -/
theorem dvd_dot_of_mem_watsonSub {Q : QuadForm ℤ n} {p : ℤ} {c : Fin n → ℤ} (hc : c ∈ watsonSub Q p)
    (t : Fin n → ℤ) : p ∣ t ⬝ᵥ (Q.hessian *ᵥ c) := by
  have h1 := (mem_watsonSub.1 hc) t
  have h2 := dvd_eval_of_mem_watsonSub hc
  rw [← QuadForm.eval_polar]
  have : Q.eval (t + c) - Q.eval t - Q.eval c = (Q.eval (t + c) - Q.eval t) - Q.eval c := by ring
  rw [this]
  exact dvd_sub h1 h2

/-- Helper: the converse description of $\Lambda_p$. -/
theorem mem_watsonSub_of {Q : QuadForm ℤ n} {p : ℤ} {c : Fin n → ℤ} (h0 : p ∣ Q.eval c)
    (h1 : ∀ t, p ∣ t ⬝ᵥ (Q.hessian *ᵥ c)) : c ∈ watsonSub Q p := by
  refine mem_watsonSub.2 fun b => ?_
  have := QuadForm.eval_polar Q b c
  have e : Q.eval (b + c) - Q.eval b = Q.eval c + b ⬝ᵥ (Q.hessian *ᵥ c) := by linear_combination this
  rw [e]
  exact dvd_add h0 (h1 b)

/-- Helper: polarization of $f(B\vec x) = 2 g(\vec x)$: $2\, x^{\mathsf T} H_g z = (Bx)^{\mathsf T} H_f (Bz)$. -/
theorem two_mul_dot_of_derived {f g : QuadForm ℤ n} {B : Matrix (Fin n) (Fin n) ℤ}
    (hg : ∀ x, f.eval (B *ᵥ x) = 2 * g.eval x) (x z : Fin n → ℤ) :
    2 * (x ⬝ᵥ (g.hessian *ᵥ z)) = (B *ᵥ x) ⬝ᵥ (f.hessian *ᵥ (B *ᵥ z)) := by
  rw [← QuadForm.eval_polar, ← QuadForm.eval_polar, ← mulVec_add, hg, hg, hg]
  ring

/-- Helper: reduction modulo $2$ of a pairing. -/
theorem redVec_dot (M : Matrix (Fin n) (Fin n) ℤ) (x z : Fin n → ℤ) :
    redVec 2 x ⬝ᵥ (M.map (algebraMap ℤ (ZMod 2)) *ᵥ redVec 2 z) = ((x ⬝ᵥ (M *ᵥ z) : ℤ) : ZMod 2) := by
  simp [redVec_apply, dotProduct, mulVec, Int.cast_sum, Int.cast_mul]

theorem redVec_mulVec (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    redVec 2 (M *ᵥ x) = M.map (Int.castRingHom (ZMod 2)) *ᵥ redVec 2 x := by
  funext i
  simp [redVec_apply, mulVec, dotProduct, Int.cast_sum, Int.cast_mul]

theorem zmod2_cast_eq_zero {a : ℤ} : ((a : ℤ) : ZMod 2) = 0 ↔ (2 : ℤ) ∣ a := by
  exact_mod_cast ZMod.intCast_zmod_eq_zero_iff_dvd a 2

/-- Helper: $y \in \Lambda$ lies in the radical modulo $2$ of the derived form criterion. -/
theorem redVec_mem_radModP_of {g : QuadForm ℤ n} {x : Fin n → ℤ} (h0 : (2 : ℤ) ∣ g.eval x)
    (h1 : ∀ z, (2 : ℤ) ∣ x ⬝ᵥ (g.hessian *ᵥ z)) : redVec 2 x ∈ radModP 2 g := by
  refine (mem_radModP 2).2 ⟨?_, fun zb => ?_⟩
  · have := evalIn_intCast_vec (S := ZMod 2) g x
    rw [show (fun i => ((x i : ℤ) : ZMod 2)) = redVec 2 x from rfl] at this
    rw [this, zmod2_cast_eq_zero]
    exact h0
  · obtain ⟨z, rfl⟩ := redVec_surjective 2 zb
    rw [redVec_dot, zmod2_cast_eq_zero]
    exact h1 z

/-- **Minimal forms are square-free at $2$, over $\mathbb Z$** (Watson 1963, §2, p. 551). Let $f$ be Watson-minimal
positive definite and $y \in \mathbb Z^n$ with $4 \mid f(y)$, $H_f y \equiv 0 \pmod 2$ and
$z^{\mathsf T} H_f y \equiv 0 \pmod 4$ for every $z \in \Lambda_2(f)$. Then every coordinate of $y$ is even.
*Proof:* $y = Bx$ with $B$ a basis matrix of $\Lambda_2(f)$ and $g$ derived. The kernel $K$ of $B$ modulo $2$ has
dimension $\ge r_2(f)$ (its image lies in $R_2(f)$) and lies in $R_2(g)$; $\bar x \in R_2(g)$ by the hypotheses. If
$y \not\equiv 0$, then $\bar x \notin K$, so $\dim R_2(g) > r_2(f)$, i.e. $r_2(f) + r_2(g) < n$, against
minimality. -/
@[kb "watson1963" "§2, proof of Theorem 2, p. 551 (minimal forms are square-free at 2)"]
theorem IsWatsonMinimal.sqFree_int {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (y : Fin n → ℤ) (h3 : (4 : ℤ) ∣ f.eval y) (h1 : ∀ w, (2 : ℤ) ∣ w ⬝ᵥ (f.hessian *ᵥ y))
    (h4 : ∀ z ∈ watsonSub f 2, (4 : ℤ) ∣ z ⬝ᵥ (f.hessian *ᵥ y)) : ∀ i, (2 : ℤ) ∣ y i := by
  classical
  by_contra hy
  push Not at hy
  obtain ⟨B, g, -, hrange, hg, hn⟩ := IsWatsonMinimal.exists_derived_rank_ge 2 hf hmin
  have hg' : ∀ x, f.eval (B *ᵥ x) = 2 * g.eval x := fun x => by exact_mod_cast hg x
  have hyW : y ∈ watsonSub f ((2 : ℕ) : ℤ) :=
    mem_watsonSub_of (dvd_trans ⟨2, by norm_num⟩ h3) h1
  have hBW : ∀ z, B *ᵥ z ∈ watsonSub f ((2 : ℕ) : ℤ) := fun z => by
    have : B *ᵥ z ∈ Set.range B.mulVec := ⟨z, rfl⟩
    rw [hrange] at this
    exact this
  obtain ⟨x, hx⟩ : y ∈ Set.range B.mulVec := by rw [hrange]; exact hyW
  set Bm := B.map (Int.castRingHom (ZMod 2))
  set K := LinearMap.ker Bm.mulVecLin
  -- (1) K ≤ R₂(g)
  have hK : K ≤ radModP 2 g := by
    intro xb hxb
    obtain ⟨x0, rfl⟩ := redVec_surjective 2 xb
    have hz : ∀ i, (2 : ℤ) ∣ (B *ᵥ x0) i := fun i => by
      have : Bm *ᵥ redVec 2 x0 = 0 := hxb
      rw [← redVec_mulVec] at this
      have := congrFun this i
      rw [redVec_apply] at this
      exact zmod2_cast_eq_zero.1 this
    choose t ht using hz
    have hBt : B *ᵥ x0 = (2 : ℤ) • t := funext fun i => by rw [ht i]; rfl
    refine redVec_mem_radModP_of ?_ fun z => ?_
    · have e := hg' x0
      rw [hBt, show f.eval ((2 : ℤ) • t) = (2 : ℤ) ^ 2 * f.eval t from evalIn_smul' f 2 t] at e
      exact ⟨f.eval t, by linarith⟩
    · have e := two_mul_dot_of_derived hg' x0 z
      rw [hBt, smul_dotProduct, smul_eq_mul] at e
      obtain ⟨c, hc⟩ := dvd_dot_of_mem_watsonSub (hBW z) t
      exact ⟨c, by push_cast at hc; linarith⟩
  -- (2) xb ∈ R₂(g)
  have hxR : redVec 2 x ∈ radModP 2 g := by
    refine redVec_mem_radModP_of ?_ fun z => ?_
    · have e := hg' x
      rw [hx] at e
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by linarith⟩
    · have e := two_mul_dot_of_derived hg' x z
      rw [hx] at e
      have hsym : y ⬝ᵥ (f.hessian *ᵥ (B *ᵥ z)) = (B *ᵥ z) ⬝ᵥ (f.hessian *ᵥ y) := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hessian_isSymm', dotProduct_comm]
      obtain ⟨c, hc⟩ := h4 _ (hBW z)
      exact ⟨c, by linarith⟩
  -- (3) xb ∉ K
  have hxK : redVec 2 x ∉ K := by
    intro h
    have : Bm *ᵥ redVec 2 x = 0 := h
    rw [← redVec_mulVec, hx] at this
    obtain ⟨i, hi⟩ := hy
    exact hi (zmod2_cast_eq_zero.1 (by rw [← redVec_apply]; exact congrFun this i))
  -- (4) dim K ≥ r₂(f)
  have hrange_le : LinearMap.range Bm.mulVecLin ≤ radModP 2 f := by
    rintro _ ⟨zb, rfl⟩
    obtain ⟨z, rfl⟩ := redVec_surjective 2 zb
    show Bm *ᵥ redVec 2 z ∈ radModP 2 f
    rw [← redVec_mulVec]
    exact (mem_watsonSub_iff_redVec_mem 2).1 (hBW z)
  have e1 := LinearMap.finrank_range_add_finrank_ker Bm.mulVecLin
  have e2 := Submodule.finrank_mono hrange_le
  have e3 := rankModP_add_finrank 2 f
  have e4 := rankModP_add_finrank 2 g
  simp only [Module.finrank_fin_fun] at e1
  -- (5) K < K ⊔ span{xb} ≤ R₂(g)
  have hlt : K < K ⊔ Submodule.span (ZMod 2) {redVec 2 x} := by
    refine lt_of_le_of_ne le_sup_left fun h => hxK ?_
    rw [h]
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  have hle : K ⊔ Submodule.span (ZMod 2) {redVec 2 x} ≤ radModP 2 g :=
    sup_le hK ((Submodule.span_singleton_le_iff_mem _ _).2 hxR)
  have e5 := Submodule.finrank_lt_finrank_of_lt hlt
  have e6 := Submodule.finrank_mono hle
  have e7 : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) (LinearMap.ker Bm.mulVecLin) := rfl
  omega

/-! ### Over $\mathbb Z_2$ -/

/-- **Watson's lattice $\Lambda_2$ over $\mathbb Z_2$:** $y$ with $2 \mid F(y)$ and $w^{\mathsf T} H_F y$ even for all
$w$. Arguments: the form `F` over $\mathbb Z_2$, the vector `y`. -/
def InLam2 (F : QuadForm ℤ_[2] n) (y : Fin n → ℤ_[2]) : Prop :=
  (2 : ℤ_[2]) ∣ F.eval y ∧ ∀ w, (2 : ℤ_[2]) ∣ w ⬝ᵥ (F.hessian *ᵥ y)

/-- **Square-free at $2$** (Watson 1963, (2.6) at $p = 2$, in the form proved by `IsWatsonMinimal.sqFree_int`): every
$y \in \Lambda_2(F)$ (`InLam2`) with $4 \mid F(y)$ and $z^{\mathsf T} H_F y \equiv 0 \pmod 4$ for all
$z \in \Lambda_2(F)$ is $\equiv 0 \pmod 2$. Argument: the form `F` over $\mathbb Z_2$. -/
@[kb "watson1963" "§2, (2.5)–(2.6), p. 551 (p-adically square-free, p = 2)"]
def SqFree2 (F : QuadForm ℤ_[2] n) : Prop :=
  ∀ y, InLam2 F y → (4 : ℤ_[2]) ∣ F.eval y → (∀ z, InLam2 F z → (4 : ℤ_[2]) ∣ z ⬝ᵥ (F.hessian *ᵥ y)) →
    ∀ i, (2 : ℤ_[2]) ∣ y i

theorem dvd_two_pow_iff_toZModPow (k : ℕ) (x : ℤ_[2]) :
    (2 : ℤ_[2]) ^ k ∣ x ↔ PadicInt.toZModPow k x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  norm_num

theorem intCast_dvd_two_pow_iff (k : ℕ) (m : ℤ) :
    (2 : ℤ_[2]) ^ k ∣ (m : ℤ_[2]) ↔ (2 : ℤ) ^ k ∣ m := by
  rw [dvd_two_pow_iff_toZModPow, map_intCast]
  have := ZMod.intCast_zmod_eq_zero_iff_dvd m (2 ^ k)
  push_cast at this
  exact this

theorem exists_int_approx_four (a : ℤ_[2]) : ∃ k : ℤ, (4 : ℤ_[2]) ∣ a - k := by
  refine ⟨((PadicInt.toZModPow 2 a).val : ℤ), ?_⟩
  rw [show (4 : ℤ_[2]) = 2 ^ 2 by norm_num, dvd_two_pow_iff_toZModPow, map_sub, map_intCast]
  simp

theorem four_dvd_iff' (x : ℤ_[2]) : (4 : ℤ_[2]) ∣ x ↔ (2 : ℤ_[2]) ^ 2 ∣ x := by norm_num

/-- **Minimal forms are square-free at $2$ over $\mathbb Z_2$** (`SqFree2`, from `IsWatsonMinimal.sqFree_int` by
reducing modulo $4$). Arguments: `hf` positive definiteness, `hmin` minimality. -/
@[kb "watson1963" "§2, proof of Theorem 2, p. 551 (minimal forms are 2-adically square-free)"]
theorem IsWatsonMinimal.sqFree2 {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f) :
    SqFree2 (f.map (Int.castRingHom ℤ_[2])) := by
  classical
  set F := f.map (Int.castRingHom ℤ_[2]) with hF
  have hH : F.hessian = f.hessian.map (Int.castRingHom ℤ_[2]) := QuadForm.hessian_map _ _
  have hev : ∀ x : Fin n → ℤ, F.eval (fun i => (x i : ℤ_[2])) = ((f.eval x : ℤ) : ℤ_[2]) := fun x => by
    rw [eval_map_padic]; exact evalIn_intCast_vec f x
  have hdot : ∀ x z : Fin n → ℤ, (fun i => (x i : ℤ_[2])) ⬝ᵥ (F.hessian *ᵥ fun i => (z i : ℤ_[2])) =
      ((x ⬝ᵥ (f.hessian *ᵥ z) : ℤ) : ℤ_[2]) := fun x z => by
    rw [hH]; simp [dotProduct, mulVec, Int.cast_sum, Int.cast_mul]
  intro y hy h4y hz
  choose k hk using fun i => exists_int_approx_four (y i)
  choose e he using hk
  -- y = k + 4 e
  have hyke : y = (fun i => (k i : ℤ_[2])) + (4 : ℤ_[2]) • e := funext fun i => by
    simp [← he i]
  set yk : Fin n → ℤ_[2] := fun i => (k i : ℤ_[2])
  have hval : F.eval y = F.eval yk + 4 * (yk ⬝ᵥ (F.hessian *ᵥ e)) + 16 * F.eval e := by
    rw [hyke]
    have h1 := QuadForm.eval_polar F yk ((4 : ℤ_[2]) • e)
    have h2 : F.eval ((4 : ℤ_[2]) • e) = (4 : ℤ_[2]) ^ 2 * F.eval e := by
      exact eval_smul_sq F 4 e
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul] at h1
    linear_combination h1 + h2
  have hdotk : ∀ w, w ⬝ᵥ (F.hessian *ᵥ y) = w ⬝ᵥ (F.hessian *ᵥ yk) + 4 * (w ⬝ᵥ (F.hessian *ᵥ e)) := by
    intro w
    rw [hyke, mulVec_add, dotProduct_add, mulVec_smul, dotProduct_smul, smul_eq_mul]
  -- the integer hypotheses
  have i3 : (4 : ℤ) ∣ f.eval k := by
    have : (4 : ℤ_[2]) ∣ F.eval yk := by
      have := (dvd_sub h4y (dvd_add (dvd_mul_right (4 : ℤ_[2]) (yk ⬝ᵥ (F.hessian *ᵥ e))) (⟨4 * F.eval e, by ring⟩ : (4 : ℤ_[2]) ∣ 16 * F.eval e)))
      rw [hval] at this
      simpa using this
    rw [hev] at this
    have h := (intCast_dvd_two_pow_iff 2 (f.eval k)).1 (by simpa [four_dvd_iff'] using this)
    simpa using h
  have i1 : ∀ w, (2 : ℤ) ∣ w ⬝ᵥ (f.hessian *ᵥ k) := by
    intro w
    have h := hy.2 (fun i => (w i : ℤ_[2]))
    rw [hdotk, hdot] at h
    have h' : (2 : ℤ_[2]) ∣ ((w ⬝ᵥ (f.hessian *ᵥ k) : ℤ) : ℤ_[2]) := by
      have := dvd_sub h (⟨2 * ((fun i => (w i : ℤ_[2])) ⬝ᵥ (F.hessian *ᵥ e)), by ring⟩ : (2 : ℤ_[2]) ∣ 4 * ((fun i => (w i : ℤ_[2])) ⬝ᵥ (F.hessian *ᵥ e)))
      simpa using this
    have := (intCast_dvd_two_pow_iff 1 _).1 (by simpa using h')
    simpa using this
  have i4 : ∀ z ∈ watsonSub f 2, (4 : ℤ) ∣ z ⬝ᵥ (f.hessian *ᵥ k) := by
    intro z hzW
    have hzL : InLam2 F (fun i => (z i : ℤ_[2])) := by
      refine ⟨?_, fun w => ?_⟩
      · rw [hev]
        exact (intCast_dvd_two_pow_iff 1 _).2 (by simpa using dvd_eval_of_mem_watsonSub hzW)
      · have hc : ∀ i, (2 : ℤ) ∣ (f.hessian *ᵥ z) i := fun i => by
          have := dvd_dot_of_mem_watsonSub hzW (Pi.single i 1)
          simpa [dotProduct, Pi.single_apply] using this
        rw [hH]
        refine Finset.dvd_sum fun i _ => ?_
        refine Dvd.dvd.mul_left ?_ _
        have : (f.hessian.map (Int.castRingHom ℤ_[2]) *ᵥ fun i => (z i : ℤ_[2])) i =
            (((f.hessian *ᵥ z) i : ℤ) : ℤ_[2]) := by simp [mulVec, dotProduct]
        rw [this]
        exact (intCast_dvd_two_pow_iff 1 _).2 (by simpa using hc i)
    have h := hz _ hzL
    rw [hdotk, hdot] at h
    have h' : (4 : ℤ_[2]) ∣ ((z ⬝ᵥ (f.hessian *ᵥ k) : ℤ) : ℤ_[2]) := by
      have := dvd_sub h (dvd_mul_right (4 : ℤ_[2]) ((fun i => (z i : ℤ_[2])) ⬝ᵥ (F.hessian *ᵥ e)))
      simpa using this
    have := (intCast_dvd_two_pow_iff 2 _).1 (by simpa [four_dvd_iff'] using h')
    simpa using this
  have hk2 := IsWatsonMinimal.sqFree_int hf hmin k i3 i1 (by simpa using i4)
  intro i
  have hyi : y i = (k i : ℤ_[2]) + 4 * e i := by linear_combination he i
  rw [hyi]
  refine dvd_add ?_ (Dvd.dvd.mul_right ⟨2, by norm_num⟩ _)
  exact (intCast_dvd_two_pow_iff 1 _).2 (by simpa using hk2 i)

/-! ### Invariance under isometry -/

/-- **`SqFree2` is invariant under $\mathbb Z_2$-isometry.** If $F(T\vec x) = G(\vec x)$ with $T$ invertible and $F$
is square-free at $2$, so is $G$ ($y \mapsto Ty$ preserves all the conditions). -/
theorem SqFree2.of_isometricGL {F G : QuadForm ℤ_[2] n} (h : IsometricGL F G) (hF : SqFree2 F) : SqFree2 G := by
  obtain ⟨T, hT⟩ := h
  have hval : ∀ x, G.eval x = F.eval (T.val *ᵥ x) := fun x => (hT x).symm
  have hdot : ∀ x y, x ⬝ᵥ (G.hessian *ᵥ y) = (T.val *ᵥ x) ⬝ᵥ (F.hessian *ᵥ (T.val *ᵥ y)) := by
    intro x y
    rw [← QuadForm.eval_polar, ← QuadForm.eval_polar, hval, hval, hval, mulVec_add]
  have hsurj : ∀ w, ∃ w', T.val *ᵥ w' = w := fun w => ⟨(T⁻¹).val *ᵥ w, by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩
  have hL : ∀ y, InLam2 G y ↔ InLam2 F (T.val *ᵥ y) := by
    intro y
    unfold InLam2
    rw [hval]
    refine and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · obtain ⟨w', rfl⟩ := hsurj w
      rw [← hdot]; exact h w'
    · rw [hdot]; exact h _
  intro y hy h4 hz i
  have hTy := hF (T.val *ᵥ y) ((hL y).1 hy) (by rw [← hval]; exact h4) (fun z hzL => by
    obtain ⟨z', rfl⟩ := hsurj z
    rw [← hdot]
    exact hz z' ((hL z').2 hzL))
  have : y = (T⁻¹).val *ᵥ (T.val *ᵥ y) := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [this]
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hTy j) _

end QuadFormsKB.Watson1963
