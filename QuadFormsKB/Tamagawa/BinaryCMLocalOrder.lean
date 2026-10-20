import QuadFormsKB.Tamagawa.BinaryCMLocalCount

/-!
# The local maximal order $\mathcal O_{E,\mathfrak p}$ in coordinates

**Layer:** as in `BinaryCMMass.lean` ($Q = \langle1,D\rangle$, `latE` $= c^{-1}(\mathcal O_E)$), at a finite prime $\mathfrak p$ of $F$, with
$\mathfrak o = \mathfrak o_\mathfrak p$, $\varpi$ = `NF.π`, $\tau = \varpi^{-1} \in F_\mathfrak p$, $d$ = the image of $D$.

**Proves** the structure of $\Lambda = (\texttt{latE})_\mathfrak p \subseteq F_\mathfrak p^2$:
* `rotMat_mulVec_mem_loc`: $\Lambda$ is closed under the multiplication of $F_\mathfrak p[\sqrt{-d}]$ (in coordinates);
* `valued_le_one_of_mem_loc`: $\Lambda \cap (F_\mathfrak p \times 0) = \mathfrak o \times 0$ (elements of an order are integral);
* **`exists_struct_loc`**: there are $c \in \mathbb N$ and $s, a, b \in \mathfrak o$ with $\varpi^{2c}a = -(s^2 + d)$, $\varpi^cb = 2s$, and
  $$\Lambda = \{(x + ts\tau^c,\ t\tau^c) : x, t \in \mathfrak o\},$$
  i.e. $\Lambda = \mathfrak o[\omega]$ with $\omega = (s + \sqrt{-d})/\varpi^c$, $\omega^2 = a + b\omega$, and $\mathfrak o^2 = \mathfrak o[\sqrt{-d}] = \mathfrak o + \varpi^c\Lambda$.

Source: Neukirch 1999, Ch. I §2 / Ch. II §2 (orders of rank $2$ over a DVR) [unverified].

-/

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne Loc LocalDensity

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- $\varpi$ in $F_\mathfrak p$. -/
abbrev πF : v.adicCompletion F := ((πv v : v.adicCompletionIntegers F) : v.adicCompletion F)

theorem valued_πF : Valued.v (πF v) = exp (-1 : ℤ) := NF.valued_π v

theorem πF_ne_zero : πF v ≠ 0 := by
  intro h; have := valued_πF v; rw [h, map_zero] at this; exact exp_ne_zero this.symm

/-! ### $\Lambda$ is an order -/

theorem rotMat_add {R : Type*} [CommRing R] (d p q p' q' : R) :
    rotMat d (p + p') (q + q') 1 = rotMat d p q 1 + rotMat d p' q' 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat] <;> ring

theorem rotMat_smul {R : Type*} [CommRing R] (d c p q : R) :
    rotMat d (c * p) (c * q) 1 = c • rotMat d p q 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat] <;> ring

/-- **$\Lambda = (\mathcal O_E)_\mathfrak p$ is closed under multiplication** (in coordinates: $y \cdot w = \mathrm{rotMat}(d, y_0, y_1, 1)\,w$). -/
theorem rotMat_mulVec_mem_loc {y w : Fin 2 → v.adicCompletion F} (hy : y ∈ loc v (latE S))
    (hw : w ∈ loc v (latE S)) : rotMat (dIn D (v.adicCompletion F)) (y 0) (y 1) 1 *ᵥ w ∈ loc v (latE S) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 : rotMat (dIn D (v.adicCompletion F)) (locVec v x 0) (locVec v x 1) 1 =
        (mulMat S (cE S x)).map (algebraMap F (v.adicCompletion F)) := by
      rw [mulMat_map, coordOf_cE]; rfl
    rw [h1]
    exact mulVec_mem_loc v (fun z hz => mulMat_mem_latE S ((mem_latE S).mp hx) hz) hw
  | zero =>
    have : rotMat (dIn D (v.adicCompletion F)) ((0 : Fin 2 → v.adicCompletion F) 0)
        ((0 : Fin 2 → v.adicCompletion F) 1) 1 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]
    rw [this, zero_mulVec]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [Pi.add_apply, Pi.add_apply, rotMat_add, add_mulVec]
    exact Submodule.add_mem _ ha hb
  | smul c m _ hm =>
    rw [show (c • m : Fin 2 → v.adicCompletion F) 0 = (c : v.adicCompletion F) * m 0 from rfl,
      show (c • m : Fin 2 → v.adicCompletion F) 1 = (c : v.adicCompletion F) * m 1 from rfl,
      rotMat_smul, smul_mulVec]
    exact Submodule.smul_mem _ c hm

theorem e1_mem_std : (![0, 1] : Fin 2 → v.adicCompletion F) ∈ std v := by
  intro i; fin_cases i <;> simp

theorem mem_loc_of_mem_std {y : Fin 2 → v.adicCompletion F} (hy : y ∈ std v) : y ∈ loc v (latE S) :=
  std_le_loc_latE S v hy

/-- $\Lambda$ is bounded: $\Lambda \subseteq \varpi^{-M}\mathfrak o^2$. -/
theorem exists_bound_loc : ∃ M : ℕ, ∀ y ∈ loc v (latE S), ∀ i, Valued.v (y i) ≤ exp (M : ℤ) := by
  obtain ⟨d, hd, -, h2⟩ := exists_global_bounds (latE_isLattice S)
  obtain ⟨k, hk⟩ := exists_valued_int_eq v hd
  refine ⟨k, fun y hy i => ?_⟩
  have := loc_le_ball v h2 hk hy i
  simpa using this

/-- **Integral elements of the order:** $(x, 0) \in \Lambda \Rightarrow v(x) \le 1$ (the powers $(x^n, 0)$ stay in the bounded $\Lambda$). -/
theorem valued_le_one_of_mem_loc {x : v.adicCompletion F} (hx : ![x, 0] ∈ loc v (latE S)) :
    Valued.v x ≤ 1 := by
  obtain ⟨M, hM⟩ := exists_bound_loc S v
  have hpow : ∀ n : ℕ, ![x ^ (n + 1), 0] ∈ loc v (latE S) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have := rotMat_mulVec_mem_loc S v hx ih
      convert this using 1
      funext i; fin_cases i <;> simp [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pow_succ] <;> ring
  by_contra hlt
  push Not at hlt
  have hx0 : x ≠ 0 := by rintro rfl; simp at hlt
  obtain ⟨m, hm⟩ := exists_valued_eq_exp v hx0
  rw [hm, ← exp_zero, exp_lt_exp] at hlt
  have := hM _ (hpow M) 0
  simp only [Matrix.cons_val_zero, map_pow, hm] at this
  rw [← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

/-! ### $\Lambda = \mathfrak o + \mathfrak o\,\omega$ -/

theorem valued_πF_pow (c : ℕ) : Valued.v (πF v ^ c) = exp (-(c : ℤ)) := by
  rw [map_pow, valued_πF, ← WithZero.exp_nsmul]; congr 1; simp

theorem valued_mul_πF_pow_le_one_iff (z : v.adicCompletion F) (c : ℕ) :
    Valued.v (z * πF v ^ c) ≤ 1 ↔ Valued.v z ≤ exp (c : ℤ) := by
  rw [map_mul, valued_πF_pow]
  constructor
  · intro h
    calc Valued.v z = Valued.v z * exp (-(c : ℤ)) * exp (c : ℤ) := by
          rw [mul_assoc, ← exp_add]; simp
      _ ≤ 1 * exp (c : ℤ) := mul_le_mul_left h _
      _ = exp (c : ℤ) := one_mul _
  · intro h
    calc Valued.v z * exp (-(c : ℤ)) ≤ exp (c : ℤ) * exp (-(c : ℤ)) := mul_le_mul_left h _
      _ = 1 := by rw [← exp_add]; simp

/-- The coordinates of $x + t\omega$, $\omega = (s\tau^c, \tau^c)$, $\tau = \varpi^{-1}$. -/
def omegaVec (c : ℕ) (s x t : v.adicCompletionIntegers F) : Fin 2 → v.adicCompletion F :=
  ![(x : v.adicCompletion F) + (t : v.adicCompletion F) * (s : v.adicCompletion F) * (πF v)⁻¹ ^ c,
    (t : v.adicCompletion F) * (πF v)⁻¹ ^ c]

theorem dIn_eq_ι : dIn D (v.adicCompletion F) = ((NF.ι v D : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  rw [dIn, ← IsScalarTower.algebraMap_apply]; rfl

set_option maxHeartbeats 1600000 in
/-- **The local maximal order in coordinates:** $\Lambda = \{(x + ts\tau^c, t\tau^c)\}$ with $\varpi^{2c}a = -(s^2 + d)$ and
$\varpi^cb = 2s$ for some $c$, $s, a, b \in \mathfrak o$. *Proof:* the second coordinates of $\Lambda$ form $\varpi^{-c}\mathfrak o$ ($c$ the largest
exponent, `Nat.findGreatest`; $\Lambda$ is bounded); a vector $\omega \in \Lambda$ with second coordinate $\varpi^{-c}$ completes $(1,0)$ to a basis
because $\Lambda \cap (F_\mathfrak p \times 0) = \mathfrak o$ (`valued_le_one_of_mem_loc`); $s, a, b$ are integral because $(0,1)$ and $\omega^2$ lie
in $\Lambda$. -/
theorem exists_struct_loc : ∃ (c : ℕ) (s a b : v.adicCompletionIntegers F),
    πv v ^ (2 * c) * a = -(s ^ 2 + NF.ι v D) ∧ πv v ^ c * b = 2 * s ∧
      ∀ y : Fin 2 → v.adicCompletion F, y ∈ loc v (latE S) ↔ ∃ x t : v.adicCompletionIntegers F, y = omegaVec v c s x t := by
  classical
  set Λ := loc v (latE S)
  obtain ⟨M, hM⟩ := exists_bound_loc S v
  let P : ℕ → Prop := fun n => ∃ y ∈ Λ, Valued.v (y 1) = exp (n : ℤ)
  have hP0 : P 0 := ⟨![0, 1], mem_loc_of_mem_std S v (e1_mem_std v), by simp⟩
  set c := Nat.findGreatest P M with hc
  have hPc : P c := Nat.findGreatest_spec (Nat.zero_le M) hP0
  have hmax : ∀ y ∈ Λ, Valued.v (y 1) ≤ exp (c : ℤ) := by
    intro y hy
    by_cases h0 : y 1 = 0
    · rw [h0, map_zero]; exact zero_le
    obtain ⟨n, hn⟩ := exists_valued_eq_exp v h0
    by_contra hlt
    push Not at hlt
    rw [hn, exp_lt_exp] at hlt
    have hnM : n ≤ M := by
      have := hM y hy 1
      rwa [hn, exp_le_exp] at this
    have hn0 : 0 ≤ n := by omega
    have hcn : c < n.toNat := by omega
    exact Nat.findGreatest_is_greatest hcn (by omega) ⟨y, hy, by rw [hn]; congr 1; omega⟩
  obtain ⟨y₀, hy₀, hv₀⟩ := hPc
  have hy₀1 : y₀ 1 ≠ 0 := by intro h; rw [h, map_zero] at hv₀; exact exp_ne_zero hv₀.symm
  have hπc : πF v ^ c ≠ 0 := pow_ne_zero _ (πF_ne_zero v)
  -- normalize ω
  set u : v.adicCompletion F := (y₀ 1 * πF v ^ c)⁻¹
  have hu : Valued.v u ≤ 1 := by
    rw [map_inv₀, map_mul, hv₀, valued_πF_pow, ← exp_add]; simp
  set uO : v.adicCompletionIntegers F := toO v u hu
  set ω : Fin 2 → v.adicCompletion F := uO • y₀
  have hω : ω ∈ Λ := Submodule.smul_mem _ _ hy₀
  have hω1 : ω 1 = (πF v)⁻¹ ^ c := by
    show u * y₀ 1 = _
    simp only [u]
    rw [inv_pow]; field_simp
  set α := ω 0
  -- s
  have hθ : (![0, 1] : Fin 2 → v.adicCompletion F) - (πv v ^ c) • ω ∈ Λ :=
    Submodule.sub_mem _ (mem_loc_of_mem_std S v (e1_mem_std v)) (Submodule.smul_mem _ _ hω)
  have hθ' : (![0, 1] : Fin 2 → v.adicCompletion F) - (πv v ^ c) • ω = ![-(πF v ^ c * α), 0] := by
    funext i; fin_cases i
    · show (0 : v.adicCompletion F) - ((πv v ^ c : v.adicCompletionIntegers F) : v.adicCompletion F) * ω 0 =
        -(πF v ^ c * α)
      push_cast; ring
    · show (1 : v.adicCompletion F) - ((πv v ^ c : v.adicCompletionIntegers F) : v.adicCompletion F) * ω 1 = 0
      rw [hω1, show ((πv v ^ c : v.adicCompletionIntegers F) : v.adicCompletion F) = πF v ^ c by push_cast; rfl,
        inv_pow, mul_inv_cancel₀ hπc, sub_self]
  rw [hθ'] at hθ
  have hs : Valued.v (πF v ^ c * α) ≤ 1 := by
    have := valued_le_one_of_mem_loc S v hθ
    rwa [Valuation.map_neg] at this
  set sO : v.adicCompletionIntegers F := toO v _ hs
  have hsα : (sO : v.adicCompletion F) * (πF v)⁻¹ ^ c = α := by
    show πF v ^ c * α * (πF v)⁻¹ ^ c = α
    rw [inv_pow]; field_simp
  -- the basis property
  have hdecomp : ∀ y : Fin 2 → v.adicCompletion F, y ∈ Λ ↔
      ∃ x t : v.adicCompletionIntegers F, y = omegaVec v c sO x t := by
    intro y
    constructor
    · intro hy
      have ht : Valued.v (y 1 * πF v ^ c) ≤ 1 := (valued_mul_πF_pow_le_one_iff v _ c).mpr (hmax y hy)
      set t : v.adicCompletionIntegers F := toO v _ ht
      have hyt : y - t • ω ∈ Λ := Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hω)
      have hyt' : y - t • ω = ![y 0 - (t : v.adicCompletion F) * α, 0] := by
        funext i; fin_cases i
        · rfl
        · show y 1 - (t : v.adicCompletion F) * ω 1 = 0
          rw [hω1]
          show y 1 - y 1 * πF v ^ c * (πF v)⁻¹ ^ c = 0
          rw [inv_pow]; field_simp; ring
      rw [hyt'] at hyt
      have hx := valued_le_one_of_mem_loc S v hyt
      refine ⟨toO v _ hx, t, ?_⟩
      funext i; fin_cases i
      · show y 0 = (y 0 - (t : v.adicCompletion F) * α) + (t : v.adicCompletion F) * (sO : v.adicCompletion F) *
          (πF v)⁻¹ ^ c
        rw [mul_assoc, hsα]; ring
      · show y 1 = y 1 * πF v ^ c * (πF v)⁻¹ ^ c
        rw [inv_pow]; field_simp
    · rintro ⟨x, t, rfl⟩
      have h1 : (x • ![1, 0] : Fin 2 → v.adicCompletion F) + t • ω ∈ Λ :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_loc_of_mem_std S v (e0_mem_std v)))
          (Submodule.smul_mem _ _ hω)
      convert h1 using 1
      funext i; fin_cases i
      · show (x : v.adicCompletion F) + (t : v.adicCompletion F) * (sO : v.adicCompletion F) * (πF v)⁻¹ ^ c =
          (x : v.adicCompletion F) * 1 + (t : v.adicCompletion F) * α
        rw [mul_assoc, hsα]; ring
      · show (t : v.adicCompletion F) * (πF v)⁻¹ ^ c = (x : v.adicCompletion F) * 0 + (t : v.adicCompletion F) * ω 1
        rw [hω1]; ring
  -- b and a from ω²
  have hω2 := rotMat_mulVec_mem_loc S v hω hω
  have hω2e : rotMat (dIn D (v.adicCompletion F)) (ω 0) (ω 1) 1 *ᵥ ω =
      ![α ^ 2 - dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2, 2 * α * (πF v)⁻¹ ^ c] := by
    funext i; fin_cases i <;> simp [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hω1, α] <;> ring
  rw [hω2e] at hω2
  have hb : Valued.v (2 * α) ≤ 1 := by
    have h := hmax _ hω2
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    rw [← valued_mul_πF_pow_le_one_iff v _ c] at h
    rwa [show 2 * α * (πF v)⁻¹ ^ c * πF v ^ c = 2 * α by rw [inv_pow]; field_simp] at h
  set bO : v.adicCompletionIntegers F := toO v _ hb
  have hω2b : ![α ^ 2 - dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2, 2 * α * (πF v)⁻¹ ^ c] - bO • ω ∈ Λ :=
    Submodule.sub_mem _ hω2 (Submodule.smul_mem _ _ hω)
  have hω2b' : ![α ^ 2 - dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2, 2 * α * (πF v)⁻¹ ^ c] - bO • ω =
      ![-(α ^ 2 + dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2), 0] := by
    funext i; fin_cases i
    · show α ^ 2 - dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2 - 2 * α * α =
        -(α ^ 2 + dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2)
      ring
    · show 2 * α * (πF v)⁻¹ ^ c - 2 * α * ω 1 = 0
      rw [hω1]; ring
  rw [hω2b'] at hω2b
  have ha : Valued.v (-(α ^ 2 + dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2)) ≤ 1 :=
    valued_le_one_of_mem_loc S v hω2b
  set aO : v.adicCompletionIntegers F := toO v _ ha
  refine ⟨c, sO, aO, bO, ?_, ?_, hdecomp⟩
  · apply Subtype.ext
    show πF v ^ (2 * c) * (-(α ^ 2 + dIn D (v.adicCompletion F) * ((πF v)⁻¹ ^ c) ^ 2)) =
      -((πF v ^ c * α) ^ 2 + ((NF.ι v D : v.adicCompletionIntegers F) : v.adicCompletion F))
    rw [← dIn_eq_ι, inv_pow]
    field_simp
    ring
  · apply Subtype.ext
    show πF v ^ c * (2 * α) = 2 * (πF v ^ c * α)
    ring

end QuadFormsKB.Tamagawa.BinaryCM
