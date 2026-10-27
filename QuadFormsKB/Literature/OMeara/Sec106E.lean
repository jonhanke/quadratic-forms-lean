/-
# O'Meara §106E: the lattice $E$ adjacent to $\mathbb Z^n$, and Proposition 106:11

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with the sum of squares $Q = x_0^2 + \dots + x_{n-1}^2$
(`sumSqForm n`, O'Meara's $V \cong I_n$), the completely decomposable lattice $D = \mathbb Z^n$ (`intVec`) with
orthogonal base $x_0, \dots, x_{n-1}$ (O'Meara's $x_1, \dots, x_n$, indices shifted by one), and $n \in \{8, 12, 16,
\dots\}$, i.e. $4 \mid n$ and $n \ge 8$.

**Defines** (O'Meara 1973, §106E, p. 331) the lattice
$$E = \mathbb Zy + \mathbb Z(2x_0) + \mathbb Z(x_1 - x_0) + \dots + \mathbb Z(x_{n-1} - x_{n-2}), \qquad
y = \tfrac12(x_0 + \dots + x_{n-1})$$
(`omearaE n`), the unimodular lattice adjacent to $D$ that contains $y$ (O'Meara's description after 106:7).

**Proves**
* Proposition 106:11 (`omeara106_11`): $\sum_i A_ix_i \in E$ if and only if $2A_i \in \mathbb Z$, $A_i - A_j \in \mathbb Z$
  and $\sum_i A_i \in 2\mathbb Z$;
* the consequences on p. 332: $E$ does not represent $1$ (`omearaE_not_represents_one`) and $E$ is indecomposable
  (`omearaE_indecomposable`, with `IsIndecomposable` of `Literature/OMeara/Sec105.lean`).
-/
import QuadFormsKB.Literature.OMeara.Sec105
import QuadFormsKB.Witt.Represents

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **The sum of $n$ squares** $x_0^2 + \dots + x_{n-1}^2$ over $\mathbb Q$ (O'Meara's $I_n$). -/
def sumSqForm (n : ℕ) : QuadForm ℚ n := QuadForm.diag fun _ => 1

/-- $y = \tfrac12(x_0 + \dots + x_{n-1})$. -/
def omearaEHalf (n : ℕ) : Fin n → ℚ := fun _ => 1 / 2

/-- The generators $y$, $2x_0$, $x_k - x_{k-1}$ ($1 \le k \le n - 1$) of $E$. -/
def omearaEGens (n : ℕ) : Set (Fin n → ℚ) :=
  {omearaEHalf n} ∪ {v | ∃ i : Fin n, i.val = 0 ∧ v = Pi.single i 2} ∪
    {v | ∃ i j : Fin n, j.val + 1 = i.val ∧ v = Pi.single i 1 - Pi.single j 1}

/-- **The lattice $E$** of O'Meara 1973, §106E, p. 331: $E = \mathbb Zy + \mathbb Z(2x_0) + \sum_{k \ge 1}
\mathbb Z(x_k - x_{k-1})$ with $y = \tfrac12(x_0 + \dots + x_{n-1})$. -/
@[kb "omeara1963" "§106E, p. 331 (the lattice E = Zy + Z(2x₁) + Z(x₃ − x₂) + ⋯; indices shifted)"]
def omearaE (n : ℕ) : Submodule (𝓞 ℚ) (Fin n → ℚ) := Submodule.span (𝓞 ℚ) (omearaEGens n)

private theorem sumSq_eval {n : ℕ} (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

private theorem sumSq_bil {n : ℕ} (x y : Fin n → ℚ) :
    bil (sumSqForm n) x y = 2 * ∑ i, x i * y i := by
  have h : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
    · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
  rw [bil, h, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct, smul_eq_mul]

/-- The right-hand side of 106:11. -/
private def PE (n : ℕ) (A : Fin n → ℚ) : Prop :=
  (∀ i, ∃ m : ℤ, 2 * A i = m) ∧ (∀ i j, ∃ m : ℤ, A i - A j = m) ∧ ∃ m : ℤ, ∑ i, A i = 2 * m

private theorem exists_intCast_oi (a : 𝓞 ℚ) : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
  ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
    (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩

private theorem smul_int_apply {n : ℕ} (k : ℤ) (A : Fin n → ℚ) (i : Fin n) :
    (((k : ℤ) : 𝓞 ℚ) • A) i = k * A i := by
  rw [Int.cast_smul_eq_zsmul]; simp

private theorem PE_int {n : ℕ} (a : Fin n → ℤ) (m : ℤ) (h : ∑ i, a i = 2 * m) :
    PE n (fun i => (a i : ℚ)) :=
  ⟨fun i => ⟨2 * a i, by push_cast; ring⟩, fun i j => ⟨a i - a j, by push_cast; ring⟩, m,
    by beta_reduce; exact_mod_cast h⟩

private def PEsub (n : ℕ) : Submodule (𝓞 ℚ) (Fin n → ℚ) where
  carrier := {A | PE n A}
  add_mem' := by
    rintro A B ⟨a1, a2, m, hm⟩ ⟨b1, b2, m', hm'⟩
    refine ⟨fun i => ?_, fun i j => ?_, m + m', ?_⟩
    · obtain ⟨p, hp⟩ := a1 i
      obtain ⟨q, hq⟩ := b1 i
      exact ⟨p + q, by simp only [Pi.add_apply]; push_cast; rw [mul_add, hp, hq]⟩
    · obtain ⟨p, hp⟩ := a2 i j
      obtain ⟨q, hq⟩ := b2 i j
      exact ⟨p + q, by simp only [Pi.add_apply]; push_cast; rw [← hp, ← hq]; ring⟩
    · simp only [Pi.add_apply]; rw [Finset.sum_add_distrib, hm, hm']; push_cast; ring
  zero_mem' := ⟨fun i => ⟨0, by simp⟩, fun i j => ⟨0, by simp⟩, 0, by simp⟩
  smul_mem' := by
    rintro c A ⟨a1, a2, m, hm⟩
    obtain ⟨k, rfl⟩ := exists_intCast_oi c
    refine ⟨fun i => ?_, fun i j => ?_, k * m, ?_⟩
    · obtain ⟨p, hp⟩ := a1 i
      exact ⟨k * p, by rw [smul_int_apply]; push_cast; rw [← hp]; ring⟩
    · obtain ⟨p, hp⟩ := a2 i j
      exact ⟨k * p, by rw [smul_int_apply, smul_int_apply]; push_cast; rw [← hp]; ring⟩
    · simp only [smul_int_apply]; rw [← Finset.mul_sum, hm]; push_cast; ring

private theorem PE_gens {n : ℕ} (h4 : 4 ∣ n) : ∀ g ∈ omearaEGens n, PE n g := by
  intro g hg
  rcases hg with (hg | hg) | hg
  · obtain rfl : g = omearaEHalf n := hg
    obtain ⟨k, rfl⟩ := h4
    refine ⟨fun i => ⟨1, by simp [omearaEHalf]⟩, fun i j => ⟨0, by simp [omearaEHalf]⟩, k, ?_⟩
    simp [omearaEHalf, Finset.sum_const]
    ring
  · obtain ⟨i, -, rfl⟩ := hg
    have e : (Pi.single i (2 : ℚ) : Fin n → ℚ) = fun j => (((Pi.single i (2 : ℤ) : Fin n → ℤ) j : ℤ) : ℚ) := by
      ext j; by_cases h : j = i <;> simp [h]
    rw [e]
    exact PE_int _ 1 (by simp)
  · obtain ⟨i, j, -, rfl⟩ := hg
    have e : (Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ) : Fin n → ℚ) =
        fun l => (((Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ) : Fin n → ℤ) l : ℤ) : ℚ) := by
      ext l; by_cases h : l = i <;> by_cases h' : l = j <;> simp [Pi.single_apply, h, h']
    rw [e]
    exact PE_int _ 0 (by simp [Finset.sum_sub_distrib])

private theorem PE_of_mem {n : ℕ} (h4 : 4 ∣ n) {A : Fin n → ℚ} (hA : A ∈ omearaE n) : PE n A :=
  (Submodule.span_le (p := PEsub n)).mpr (PE_gens h4) hA

private theorem single_sub_mem {n : ℕ} (hn : 0 < n) :
    ∀ t : ℕ, ∀ i : Fin n, i.val = t →
      (Pi.single i (1 : ℚ) - Pi.single (⟨0, hn⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) ∈ omearaE n := by
  intro t
  induction t with
  | zero =>
    intro i hi
    obtain rfl : i = ⟨0, hn⟩ := Fin.ext hi
    simp
  | succ t ih =>
    intro i hi
    have hj : t < n := by omega
    have h1 := ih ⟨t, hj⟩ rfl
    have g : (Pi.single i (1 : ℚ) - Pi.single (⟨t, hj⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) ∈ omearaE n :=
      Submodule.subset_span (Or.inr ⟨i, ⟨t, hj⟩, by simp [hi], rfl⟩)
    have := add_mem g h1
    convert this using 1
    abel

private theorem mem_of_int {n : ℕ} (hn : 0 < n) (a : Fin n → ℤ) (m : ℤ) (h : ∑ i, a i = 2 * m) :
    (fun i => (a i : ℚ)) ∈ omearaE n := by
  have hx0 : (Pi.single (⟨0, hn⟩ : Fin n) (2 : ℚ) : Fin n → ℚ) ∈ omearaE n :=
    Submodule.subset_span (Or.inl (Or.inr ⟨⟨0, hn⟩, rfl, rfl⟩))
  have hsum : (∑ i, (a i : ℚ)) = 2 * m := by exact_mod_cast h
  have e : (fun i => (a i : ℚ)) = ∑ i, a i • (Pi.single i (1 : ℚ) - Pi.single (⟨0, hn⟩ : Fin n) (1 : ℚ)
      : Fin n → ℚ) + m • (Pi.single (⟨0, hn⟩ : Fin n) (2 : ℚ) : Fin n → ℚ) := by
    ext k
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply]
    simp only [zsmul_eq_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [← Finset.sum_mul, hsum]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hk : k = ⟨0, hn⟩ <;> simp [hk]; ring
  rw [e]
  refine add_mem (Submodule.sum_mem _ fun i _ => ?_) (zsmul_mem hx0 _)
  exact zsmul_mem (single_sub_mem hn _ i rfl) _

private theorem dichotomy {n : ℕ} (hn : 0 < n) {A : Fin n → ℚ} (hA : PE n A) :
    (∀ i, ∃ b : ℤ, A i = b) ∨ (∀ i, ∃ b : ℤ, A i = b + 1 / 2) := by
  obtain ⟨h1, h2, -⟩ := hA
  obtain ⟨m0, hm0⟩ := h1 ⟨0, hn⟩
  rcases Int.even_or_odd' m0 with ⟨c, rfl | rfl⟩
  · left
    intro i
    obtain ⟨d, hd⟩ := h2 i ⟨0, hn⟩
    exact ⟨d + c, by push_cast at hm0 ⊢; linarith⟩
  · right
    intro i
    obtain ⟨d, hd⟩ := h2 i ⟨0, hn⟩
    exact ⟨d + c, by push_cast at hm0 ⊢; linarith⟩

private theorem mem_of_PE {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n) {A : Fin n → ℚ} (hA : PE n A) :
    A ∈ omearaE n := by
  obtain ⟨k, hk⟩ := h4
  obtain ⟨-, -, m, hm⟩ := id hA
  rcases dichotomy hn hA with h | h
  · choose a ha using h
    have : A = fun i => (a i : ℚ) := funext ha
    rw [this]
    refine mem_of_int hn a m ?_
    have : (∑ i, (a i : ℚ)) = 2 * m := by rw [← hm, this]
    exact_mod_cast this
  · choose a ha using h
    have hy : omearaEHalf n ∈ omearaE n := Submodule.subset_span (Or.inl (Or.inl rfl))
    have : A = (fun i => (a i : ℚ)) + omearaEHalf n := by
      funext i; simp [ha i, omearaEHalf]
    rw [this]
    refine add_mem ?_ hy
    refine mem_of_int hn a (m - k) ?_
    have hs : (∑ i, (a i : ℚ)) = 2 * (m - k) := by
      have : ∑ i, A i = ∑ i, ((a i : ℚ) + 1 / 2) := Finset.sum_congr rfl fun i _ => ha i
      rw [Finset.sum_add_distrib, hm] at this
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      subst hk
      push_cast at this ⊢
      linarith
    exact_mod_cast hs

/-- **Proposition 106:11** (O'Meara 1973, §106E, p. 332): for $n \in \{8, 12, \dots\}$ (here: $4 \mid n$, $n \ge 1$),
$\sum_i A_ix_i \in E$ if and only if $2A_i \in \mathbb Z$, $A_i - A_j \in \mathbb Z$ for all $i, j$, and
$\sum_i A_i \in 2\mathbb Z$. -/
@[kb "omeara1963" "§106E, 106:11, p. 332"]
theorem omeara106_11 {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n) (A : Fin n → ℚ) :
    A ∈ omearaE n ↔ (∀ i, ∃ m : ℤ, 2 * A i = m) ∧ (∀ i j, ∃ m : ℤ, A i - A j = m) ∧
      ∃ m : ℤ, ∑ i, A i = 2 * m :=
  ⟨fun hA => PE_of_mem h4 hA, fun hA => mem_of_PE h4 hn hA⟩

private theorem int_sq_sum {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n) {x : Fin n → ℚ} (hx : x ∈ omearaE n) :
    ∃ q : ℤ, ∑ i, x i ^ 2 = q := by
  have hP := PE_of_mem h4 hx
  obtain ⟨k, hk⟩ := h4
  rcases dichotomy hn hP with h | h
  · choose a ha using h
    exact ⟨∑ i, a i ^ 2, by
      push_cast; exact Finset.sum_congr rfl fun i _ => by rw [ha i]⟩
  · choose a ha using h
    refine ⟨∑ i, (a i ^ 2 + a i) + k, ?_⟩
    have : ∀ i, x i ^ 2 = ((a i ^ 2 + a i : ℤ) : ℚ) + 1 / 4 := fun i => by
      rw [ha i]; push_cast; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    subst hk
    push_cast
    rw [Finset.sum_add_distrib]
    ring

/-- **$E$ does not represent $1$** (O'Meara 1973, §106E, p. 332, after 106:11), for $n \in \{8, 12, \dots\}$. -/
@[kb "omeara1963" "§106E, p. 332 (E does not represent 1)"]
theorem omearaE_not_represents_one {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    ∀ x ∈ omearaE n, (sumSqForm n).eval x ≠ 1 := by
  intro x hx h1
  have hn : 0 < n := by omega
  rw [sumSq_eval] at h1
  have hP := PE_of_mem h4 hx
  obtain ⟨-, -, m, hm⟩ := id hP
  rcases dichotomy hn hP with h | h
  · choose a ha using h
    have h1' : ∑ i, a i ^ 2 = 1 := by
      have : ((∑ i, a i ^ 2 : ℤ) : ℚ) = 1 := by
        push_cast; rw [← h1]; exact Finset.sum_congr rfl fun i _ => by rw [ha i]
      exact_mod_cast this
    have h2' : ∑ i, a i = 2 * m := by
      have : ((∑ i, a i : ℤ) : ℚ) = 2 * m := by
        push_cast; rw [← hm]; exact Finset.sum_congr rfl fun i _ => (ha i).symm
      exact_mod_cast this
    have hd : (2 : ℤ) ∣ ∑ i, (a i ^ 2 - a i) := Finset.dvd_sum fun i _ => by
      obtain ⟨c, hc⟩ := Int.even_mul_pred_self (a i)
      exact ⟨c, by nlinarith [hc]⟩
    rw [Finset.sum_sub_distrib, h1', h2'] at hd
    omega
  · choose a ha using h
    have hq : ∀ i, (1 : ℚ) / 4 ≤ x i ^ 2 := fun i => by
      rw [ha i]
      rcases le_or_gt 0 (a i) with h0 | h0
      · have : (0 : ℚ) ≤ a i := by exact_mod_cast h0
        nlinarith
      · have : (a i : ℚ) ≤ -1 := by exact_mod_cast (by omega : a i ≤ -1)
        nlinarith
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hq i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [h1] at this
    have : (8 : ℚ) ≤ n := by exact_mod_cast h8
    linarith

/-- The indicator vector of the coordinate `t` (zero if `t ≥ n`). -/
private def ev (n t : ℕ) : Fin n → ℚ := fun i => if i.val = t then 1 else 0

private theorem ev_eq_single {n : ℕ} (t : ℕ) (ht : t < n) : ev n t = Pi.single ⟨t, ht⟩ 1 := by
  ext i; simp [ev, Pi.single_apply, Fin.ext_iff]

private theorem dot_ev {n : ℕ} (w : Fin n → ℚ) (t : ℕ) (ht : t < n) :
    ∑ i, w i * ev n t i = w ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · simp [ev]
  · intro b _ hb
    have : b.val ≠ t := fun h => hb (Fin.ext h)
    simp [ev, this]
  · simp

private theorem ip_sub {n : ℕ} (w : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n) :
    ∑ i, w i * (ev n a i - ev n b i) = w ⟨a, ha⟩ - w ⟨b, hb⟩ := by
  simp only [mul_sub, Finset.sum_sub_distrib, dot_ev w a ha, dot_ev w b hb]

private theorem ip_add {n : ℕ} (w : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n) :
    ∑ i, w i * (ev n a i + ev n b i) = w ⟨a, ha⟩ + w ⟨b, hb⟩ := by
  simp only [mul_add, Finset.sum_add_distrib, dot_ev w a ha, dot_ev w b hb]

private theorem ip_sub' {n : ℕ} (w : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n) :
    ∑ i, w i * (ev n a - ev n b) i = w ⟨a, ha⟩ - w ⟨b, hb⟩ := ip_sub w a b ha hb

private theorem ip_add' {n : ℕ} (w : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n) :
    ∑ i, w i * (ev n a + ev n b) i = w ⟨a, ha⟩ + w ⟨b, hb⟩ := ip_add w a b ha hb

private theorem R_mem{n : ℕ} (t : ℕ) (h : t + 1 < n) : ev n (t + 1) - ev n t ∈ omearaE n := by
  rw [ev_eq_single _ h, ev_eq_single _ (by omega)]
  exact Submodule.subset_span (Or.inr ⟨_, _, rfl, rfl⟩)

private theorem z_mem {n : ℕ} (hn : 2 < n) : ev n 0 + ev n 1 ∈ omearaE n := by
  have e : ev n 0 + ev n 1 = Pi.single (⟨0, by omega⟩ : Fin n) (2 : ℚ) + (ev n (0 + 1) - ev n 0) := by
    ext i
    by_cases h0 : i.val = 0
    · have : i.val ≠ 1 := by omega
      simp [ev, Pi.single_apply, Fin.ext_iff, h0]
      norm_num
    · by_cases h1 : i.val = 1
      · simp [ev, Fin.ext_iff, h1]
      · simp [ev, Fin.ext_iff, h0, h1]
  rw [e]
  exact add_mem (Submodule.subset_span (Or.inl (Or.inr ⟨⟨0, by omega⟩, rfl, rfl⟩)))
    (R_mem 0 (by omega))

private theorem sq_eq_ip {n : ℕ} (x : Fin n → ℚ) : ∑ i, x i ^ 2 = ∑ i, x i * x i := by
  simp [sq]

private theorem R_sq {n : ℕ} (t : ℕ) (h : t + 1 < n) : ∑ i, (ev n (t + 1) - ev n t) i ^ 2 = 2 := by
  rw [sq_eq_ip, ip_sub' _ (t + 1) t h (by omega)]
  simp [ev]
  norm_num

private theorem z_sq {n : ℕ} (hn : 2 < n) : ∑ i, (ev n 0 + ev n 1) i ^ 2 = 2 := by
  rw [sq_eq_ip, ip_add' _ 0 1 (by omega) (by omega)]
  simp [ev]
  norm_num

private theorem root_split {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) {K₁ K₂ : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (horth : LatOrth (sumSqForm n) K₁ K₂) (hsup : K₁ ⊔ K₂ = omearaE n) {z : Fin n → ℚ}
    (hz : z ∈ omearaE n) (hz2 : ∑ i, z i ^ 2 = 2) : z ∈ K₁ ∨ z ∈ K₂ := by
  have hn : 0 < n := by omega
  rw [← hsup] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  have hE1 : u ∈ omearaE n := hsup ▸ Submodule.mem_sup_left hu
  have hE2 : v ∈ omearaE n := hsup ▸ Submodule.mem_sup_right hv
  have hb := horth u hu v hv
  rw [sumSq_bil] at hb
  have hsq : ∑ i, (u + v) i ^ 2 = ∑ i, u i ^ 2 + ∑ i, v i ^ 2 + 2 * ∑ i, u i * v i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  have hz0 : ∑ i, u i * v i = 0 := by linarith
  have hsum : ∑ i, u i ^ 2 + ∑ i, v i ^ 2 = 2 := by
    rw [hsq, hz0] at hz2; linarith
  obtain ⟨q1, hq1⟩ := int_sq_sum h4 hn hE1
  obtain ⟨q2, hq2⟩ := int_sq_sum h4 hn hE2
  have n1 := omearaE_not_represents_one h4 h8 u hE1
  have n2 := omearaE_not_represents_one h4 h8 v hE2
  rw [sumSq_eval, hq1] at n1
  rw [sumSq_eval, hq2] at n2
  have p1 : (0 : ℚ) ≤ q1 := hq1 ▸ Finset.sum_nonneg (fun i _ => sq_nonneg (u i))
  have p2 : (0 : ℚ) ≤ q2 := hq2 ▸ Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have p1' : 0 ≤ q1 := by exact_mod_cast p1
  have p2' : 0 ≤ q2 := by exact_mod_cast p2
  have hq : q1 + q2 = 2 := by
    have : (q1 : ℚ) + q2 = 2 := by rw [← hq1, ← hq2]; exact hsum
    exact_mod_cast this
  have n1' : q1 ≠ 1 := fun h => n1 (by rw [h]; simp)
  have n2' : q2 ≠ 1 := fun h => n2 (by rw [h]; simp)
  rcases (by omega : q1 = 0 ∨ q2 = 0) with h | h
  · right
    have hu0 : u = 0 := by
      have h0 : ∑ i, u i ^ 2 = 0 := by rw [hq1, h]; simp
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i))).mp h0 i
        (Finset.mem_univ i)
      simpa using this
    rw [hu0, zero_add]; exact hv
  · left
    have hv0 : v = 0 := by
      have h0 : ∑ i, v i ^ 2 = 0 := by rw [hq2, h]; simp
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp h0 i
        (Finset.mem_univ i)
      simpa using this
    rw [hv0, add_zero]; exact hu

private theorem no_split {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) {K₁ K₂ : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (horth : LatOrth (sumSqForm n) K₁ K₂) (hsup : K₁ ⊔ K₂ = omearaE n) (hne : K₂ ≠ ⊥)
    (hz : ev n 0 + ev n 1 ∈ K₁) : False := by
  have hn : 2 < n := by omega
  have step : ∀ r ∈ K₁, ∀ r', r' ∈ omearaE n → ∑ i, r' i ^ 2 = 2 → ∑ i, r i * r' i ≠ 0 →
      r' ∈ K₁ := by
    intro r hr r' hr' hn2 hne'
    rcases root_split h4 h8 horth hsup hr' hn2 with h | h
    · exact h
    · exfalso
      apply hne'
      have := horth r hr r' h
      rw [sumSq_bil] at this
      linarith
  have h1 : ev n (1 + 1) - ev n 1 ∈ K₁ := by
    refine step _ hz _ (R_mem 1 (by omega)) (R_sq 1 (by omega)) ?_
    rw [ip_sub' _ (1 + 1) 1 (by omega) (by omega)]
    simp [ev]
  have hall : ∀ t, 1 ≤ t → t + 1 < n → ev n (t + 1) - ev n t ∈ K₁ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro _; simpa using h1
    | succ t ht ih =>
      intro hlt
      refine step _ (ih (by omega)) _ (R_mem (t + 1) hlt) (R_sq (t + 1) hlt) ?_
      rw [ip_sub' _ (t + 1 + 1) (t + 1) (by omega) (by omega)]
      have h' : ¬ (t + 1 + 1 = t) := by omega
      simp [ev, h']
  have h0 : ev n (0 + 1) - ev n 0 ∈ K₁ := by
    refine step _ (by simpa using h1) _ (R_mem 0 (by omega)) (R_sq 0 (by omega)) ?_
    rw [ip_sub' _ (0 + 1) 0 (by omega) (by omega)]
    simp [ev]
  have hR : ∀ t, t + 1 < n → ev n (t + 1) - ev n t ∈ K₁ := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · exact h0
    · exact hall t hpos ht
  apply hne
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hdiff : ∀ t (ht : t + 1 < n), w ⟨t + 1, ht⟩ = w ⟨t, by omega⟩ := by
    intro t ht
    have := horth _ (hR t ht) w hw
    rw [sumSq_bil] at this
    have e : ∑ i, (ev n (t + 1) - ev n t) i * w i = ∑ i, w i * (ev n (t + 1) i - ev n t i) :=
      Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, mul_comm]
    rw [e, ip_sub _ (t + 1) t ht (by omega)] at this
    linarith
  have hconst : ∀ t (ht : t < n), w ⟨t, ht⟩ = w ⟨0, by omega⟩ := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih => intro ht; rw [hdiff t ht, ih (by omega)]
  have hz' := horth _ hz w hw
  rw [sumSq_bil] at hz'
  have e : ∑ i, (ev n 0 + ev n 1) i * w i = ∑ i, w i * (ev n 0 i + ev n 1 i) :=
    Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_comm]
  rw [e, ip_add _ 0 1 (by omega) (by omega)] at hz'
  have h01 := hconst 1 (by omega)
  funext i
  have := hconst i.val i.isLt
  simp only [Fin.eta] at this
  rw [this]
  simp only [Pi.zero_apply]
  linarith

/-- **$E$ is indecomposable** (O'Meara 1973, §106E, p. 332), for $n \in \{8, 12, \dots\}$. -/
@[kb "omeara1963" "§106E, p. 332 (E is indecomposable)"]
theorem omearaE_indecomposable {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    IsIndecomposable (sumSqForm n) (omearaE n) := by
  have hn : 2 < n := by omega
  refine ⟨?_, ?_⟩
  · intro hbot
    have h2 : (Pi.single (⟨0, by omega⟩ : Fin n) (2 : ℚ) : Fin n → ℚ) ∈ omearaE n :=
      Submodule.subset_span (Or.inl (Or.inr ⟨⟨0, by omega⟩, rfl, rfl⟩))
    rw [hbot] at h2
    have := congrFun (Submodule.mem_bot _ |>.mp h2) ⟨0, by omega⟩
    simp at this
  · rintro ⟨K₁, K₂, h1, h2, horth, -, hsup⟩
    have hz := z_mem hn
    rcases root_split h4 h8 horth hsup hz (z_sq hn) with h | h
    · exact no_split h4 h8 horth hsup h2 h
    · refine no_split h4 h8 (K₁ := K₂) (K₂ := K₁) ?_ (by rwa [sup_comm]) h1 h
      intro x hx y hy
      have := horth y hy x hx
      rw [sumSq_bil] at this ⊢
      simpa [mul_comm] using this

end QuadFormsKB.Lattices
