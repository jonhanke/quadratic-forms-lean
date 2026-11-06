/-
# Conway–Sloane 1988, §8: the modulus, the conductor and the primitive character (Tables 4, 5)

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, pp. 267–269.

**Definitions (book $\to$ Lean).** For an integer $D \ne 0$ let $\chi_D(m) = $ `chiD D m` (see `StandardMass.lean`).
* The *modulus* $k$ of $\chi_D$ is the least positive period of $m \mapsto \chi_D(m)$: `IsModulus D k`.
* The *conductor* $k_1$ is the least positive divisor of $k$ such that $\chi_D(m)$ depends only on $m \bmod k_1$ for
  $m$ coprime to $k$ (so that $\chi_D = \chi_1\psi$ with $\chi_1$ the principal character mod $k$ and $\psi$ primitive mod $k_1$):
  `IsConductor D k k₁`. (The restriction to divisors of $k$ is a convention of this file; it holds in every case of Table 4.)
* The character $\psi$ is `psi D k k₁ m`: for $\gcd(m, k_1) = 1$ it is $\chi_D(m')$ for the first $m' \in [0, k)$ with
  $m' \equiv m \pmod{k_1}$ and $\gcd(m', k) = 1$; for $\gcd(m, k_1) > 1$ it is $0$. (This is well defined, i.e. independent of
  the choice of $m'$, exactly when `IsConductor D k k₁` holds.)

**Method.** $\chi_D$ is periodic modulo $4\lvert D\rvert$ (`chiD_mod`), so everything about it is a finite check on one period.
For each $D$ of the tables the values on $[0, 4\lvert D\rvert)$ are verified one by one (`norm_num`, with Mathlib's Jacobi
symbol evaluator) as an explicit list, and the minimality statements are then decided by `decide` on that list.

**Proves**
* `table4_*`: every entry of Table 4 (p. 269), $D = \pm1, \pm2, \pm3, \pm5, \pm6, \pm7, \pm9, \pm10, \pm11$: the modulus $k$
  and the conductor $k_1$ are exactly as printed (the least-ness is part of the statement).
* `table5_*`: the values $\psi(m)$, $1 \le m \le k_1$, of Table 5 for $\lvert D\rvert \le 9$ (the rows are listed in the
  statements, with $+ = 1$, $- = -1$).
* `zetaD_eq_L_mul` ((10), p. 268): for real $s > 1$, $\zeta_D(s) = L(s,\psi)\prod_{p \mid k}(1 - \psi(p)p^{-s})$ for any
  completely multiplicative $\psi$ agreeing with $\chi_D$ on integers coprime to $k$ (such as the primitive character of the book).
* `zetaD_neg_one_one` (Table 6): $\zeta_{-1}(1) = \pi/4$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.StandardMass
import QuadFormsKB.Binary.EulerProductAtOne

namespace QuadFormsKB.ConwaySloane.Mass

open scoped Real

/-! ### Definitions -/

/-- $k$ is a period of $\chi_D$. -/
def Per (D : ℤ) (k : ℕ) : Prop := ∀ m, chiD D (m + k) = chiD D m

/-- **The modulus** $k$ of $\chi_D$ (§8.r1): the least positive period of $m \mapsto \chi_D(m)$. -/
@[kb "conwaysloane1988" "§8, remark 1, p. 267"]
def IsModulus (D : ℤ) (k : ℕ) : Prop := 0 < k ∧ Per D k ∧ ∀ j, 0 < j → Per D j → k ≤ j

/-- $\chi_D(m)$ depends only on $m \bmod k_1$ for $m$ coprime to $k$. -/
def Respects (D : ℤ) (k k₁ : ℕ) : Prop :=
  ∀ m n, Nat.Coprime m k → Nat.Coprime n k → m % k₁ = n % k₁ → chiD D m = chiD D n

/-- **The conductor** $k_1$ of $\chi_D$ (§8.r1), relative to its modulus $k$: the least positive divisor $k_1$ of $k$ such that
$\chi_D(m)$ depends only on $m \bmod k_1$ for $m$ coprime to $k$. -/
@[kb "conwaysloane1988" "§8, remark 1, p. 267"]
def IsConductor (D : ℤ) (k k₁ : ℕ) : Prop :=
  0 < k₁ ∧ k₁ ∣ k ∧ Respects D k k₁ ∧ ∀ j, 0 < j → j ∣ k → Respects D k j → k₁ ≤ j

/-- Generic version of $\psi$ for a function `f` in place of $\chi_D$: see `psi`. -/
def psiF (f : ℕ → ℤ) (k k₁ m : ℕ) : ℤ :=
  if Nat.gcd m k₁ = 1 then
    match (List.range k).find? (fun m' => decide (m' % k₁ = m % k₁ ∧ Nat.gcd m' k = 1)) with
    | some m' => f m'
    | none => 0
  else 0

/-- **The primitive character** $\psi$ of §8 (Table 5), for modulus $k$ and conductor $k_1$ of $\chi_D$: $\psi(m) = \chi_D(m')$
for $m'$ the first integer in $[0, k)$ with $m' \equiv m \pmod{k_1}$ and $\gcd(m', k) = 1$, if $\gcd(m, k_1) = 1$; and
$\psi(m) = 0$ otherwise. -/
@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
def psi (D : ℤ) (k k₁ m : ℕ) : ℤ := psiF (chiD D) k k₁ m

/-! ### Reduction of the checks to finite ones -/

/-- The function with period `T.length` taking the values `T`. -/
def fT (T : List ℤ) (m : ℕ) : ℤ := T.getD (m % T.length) 0

theorem fT_mod (T : List ℤ) (m : ℕ) : fT T (m % T.length) = fT T m := by
  simp [fT]

theorem chiD_eq_fT (D : ℤ) (hD : D ≠ 0) (T : List ℤ) (hlen : T.length = 4 * D.natAbs)
    (h : ∀ m < T.length, chiD D m = T.getD m 0) : chiD D = fT T := by
  funext m
  have hpos : 0 < T.length := by
    rw [hlen]; have := Int.natAbs_pos.mpr hD; omega
  unfold fT
  rw [← h _ (Nat.mod_lt _ hpos), hlen, chiD_mod]

theorem per_mod {f : ℕ → ℤ} {k : ℕ} (h : ∀ m, f (m + k) = f m) (m : ℕ) : f (m % k) = f m := by
  have key : ∀ q r, f (r + k * q) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih => intro r; rw [show r + k * (q + 1) = (r + k * q) + k by ring, h, ih]
  conv_rhs => rw [← Nat.mod_add_div m k]
  exact (key _ _).symm

theorem per_of_bdd {f : ℕ → ℤ} {N : ℕ} (hf : ∀ m, f (m % N) = f m) {k : ℕ}
    (h : ∀ m < N, f (m + k) = f m) (hN : 0 < N) : ∀ m, f (m + k) = f m := by
  intro m
  rw [← hf (m + k), ← Nat.mod_add_mod m N k, hf (m % N + k)]
  rw [h _ (Nat.mod_lt _ hN), hf]

theorem isModulus_of_tab (D : ℤ) (T : List ℤ) (hT : chiD D = fT T) (hpos : 0 < T.length) (k : ℕ)
    (h0 : 0 < k) (hper : ∀ m < T.length, fT T (m + k) = fT T m)
    (hmin : ∀ j < k, 0 < j → ∃ m < T.length, fT T (m + j) ≠ fT T m) : IsModulus D k := by
  refine ⟨h0, ?_, fun j hj hPj => ?_⟩
  · intro m
    rw [hT]
    exact per_of_bdd (fT_mod T) hper hpos m
  · by_contra hlt
    push_neg at hlt
    obtain ⟨m, _, hne⟩ := hmin j hlt hj
    apply hne
    have := hPj m
    rwa [hT] at this

theorem respects_of_bdd {f : ℕ → ℤ} {k k₁ : ℕ} (hkpos : 0 < k) (hk : ∀ m, f (m % k) = f m)
    (hdvd : k₁ ∣ k)
    (h : ∀ m < k, ∀ n < k, Nat.Coprime m k → Nat.Coprime n k → m % k₁ = n % k₁ → f m = f n) :
    ∀ m n, Nat.Coprime m k → Nat.Coprime n k → m % k₁ = n % k₁ → f m = f n := by
  have hcop : ∀ m, Nat.Coprime m k → Nat.Coprime (m % k) k := by
    intro m hm
    unfold Nat.Coprime at *
    rw [← Nat.gcd_rec k m, Nat.gcd_comm]
    exact hm
  intro m n hm hn hmn
  rw [← hk m, ← hk n]
  exact h _ (Nat.mod_lt _ hkpos) _ (Nat.mod_lt _ hkpos) (hcop m hm) (hcop n hn)
    (by rw [Nat.mod_mod_of_dvd m hdvd, Nat.mod_mod_of_dvd n hdvd]; exact hmn)

theorem isConductor_of_tab (D : ℤ) (T : List ℤ) (hT : chiD D = fT T) (k k₁ : ℕ)
    (hmod : IsModulus D k) (h1 : 0 < k₁) (hdvd : k₁ ∣ k)
    (hres : ∀ m < k, ∀ n < k, Nat.Coprime m k → Nat.Coprime n k → m % k₁ = n % k₁ →
      fT T m = fT T n)
    (hmin : ∀ j < k₁, 0 < j → j ∣ k → ∃ m < k, ∃ n < k, Nat.Coprime m k ∧ Nat.Coprime n k ∧
      m % j = n % j ∧ fT T m ≠ fT T n) : IsConductor D k k₁ := by
  have hk : ∀ m, fT T (m % k) = fT T m := by
    intro m
    have := per_mod hmod.2.1 m
    rwa [hT] at this
  refine ⟨h1, hdvd, ?_, fun j hj hjk hRj => ?_⟩
  · intro m n hm hn hmn
    rw [hT]
    exact respects_of_bdd hmod.1 hk hdvd hres m n hm hn hmn
  · by_contra hlt
    push_neg at hlt
    obtain ⟨m, hm, n, hn, hcm, hcn, hmn, hne⟩ := hmin j hlt hj hjk
    apply hne
    have := hRj m n hcm hcn hmn
    rwa [hT] at this

def tab_p1 : List ℤ := [0, 1, 0, 1]

theorem chiD_eq_tab_p1 : chiD 1 = fT tab_p1 :=
  chiD_eq_fT 1 (by norm_num) tab_p1 (by decide) (by
    intro m hm
    have hm' : m < 4 := hm
    interval_cases m <;> norm_num [chiD, tab_p1])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p1 : IsModulus 1 2 ∧ IsConductor 1 2 1 := by
  have hmod : IsModulus 1 2 :=
    isModulus_of_tab 1 tab_p1 chiD_eq_tab_p1 (by decide) 2 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 1 tab_p1 chiD_eq_tab_p1 2 1 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_p1 : (List.range' 1 1).map (psi 1 2 1) = [1] := by
  unfold psi
  rw [chiD_eq_tab_p1]
  decide

def tab_p2 : List ℤ := [0, 1, 0, -1, 0, -1, 0, 1]

theorem chiD_eq_tab_p2 : chiD 2 = fT tab_p2 :=
  chiD_eq_fT 2 (by norm_num) tab_p2 (by decide) (by
    intro m hm
    have hm' : m < 8 := hm
    interval_cases m <;> norm_num [chiD, tab_p2])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p2 : IsModulus 2 8 ∧ IsConductor 2 8 8 := by
  have hmod : IsModulus 2 8 :=
    isModulus_of_tab 2 tab_p2 chiD_eq_tab_p2 (by decide) 8 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 2 tab_p2 chiD_eq_tab_p2 8 8 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_p2 : (List.range' 1 8).map (psi 2 8 8) = [1, 0, -1, 0, -1, 0, 1, 0] := by
  unfold psi
  rw [chiD_eq_tab_p2]
  decide

def tab_p3 : List ℤ := [0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1]

theorem chiD_eq_tab_p3 : chiD 3 = fT tab_p3 :=
  chiD_eq_fT 3 (by norm_num) tab_p3 (by decide) (by
    intro m hm
    have hm' : m < 12 := hm
    interval_cases m <;> norm_num [chiD, tab_p3])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p3 : IsModulus 3 12 ∧ IsConductor 3 12 12 := by
  have hmod : IsModulus 3 12 :=
    isModulus_of_tab 3 tab_p3 chiD_eq_tab_p3 (by decide) 12 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 3 tab_p3 chiD_eq_tab_p3 12 12 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_p3 : (List.range' 1 12).map (psi 3 12 12) = [1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0] := by
  unfold psi
  rw [chiD_eq_tab_p3]
  decide

def tab_p5 : List ℤ := [0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1]

theorem chiD_eq_tab_p5 : chiD 5 = fT tab_p5 :=
  chiD_eq_fT 5 (by norm_num) tab_p5 (by decide) (by
    intro m hm
    have hm' : m < 20 := hm
    interval_cases m <;> norm_num [chiD, tab_p5])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p5 : IsModulus 5 10 ∧ IsConductor 5 10 5 := by
  have hmod : IsModulus 5 10 :=
    isModulus_of_tab 5 tab_p5 chiD_eq_tab_p5 (by decide) 10 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 5 tab_p5 chiD_eq_tab_p5 10 5 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_p5 : (List.range' 1 5).map (psi 5 10 5) = [1, -1, -1, 1, 0] := by
  unfold psi
  rw [chiD_eq_tab_p5]
  decide

def tab_p6 : List ℤ := [0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1]

theorem chiD_eq_tab_p6 : chiD 6 = fT tab_p6 :=
  chiD_eq_fT 6 (by norm_num) tab_p6 (by decide) (by
    intro m hm
    have hm' : m < 24 := hm
    interval_cases m <;> norm_num [chiD, tab_p6])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p6 : IsModulus 6 24 ∧ IsConductor 6 24 24 := by
  have hmod : IsModulus 6 24 :=
    isModulus_of_tab 6 tab_p6 chiD_eq_tab_p6 (by decide) 24 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 6 tab_p6 chiD_eq_tab_p6 24 24 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_p6 : (List.range' 1 24).map (psi 6 24 24) = [1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0] := by
  unfold psi
  rw [chiD_eq_tab_p6]
  decide

def tab_p7 : List ℤ := [0, 1, 0, 1, 0, -1, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1]

theorem chiD_eq_tab_p7 : chiD 7 = fT tab_p7 :=
  chiD_eq_fT 7 (by norm_num) tab_p7 (by decide) (by
    intro m hm
    have hm' : m < 28 := hm
    interval_cases m <;> norm_num [chiD, tab_p7])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p7 : IsModulus 7 28 ∧ IsConductor 7 28 28 := by
  have hmod : IsModulus 7 28 :=
    isModulus_of_tab 7 tab_p7 chiD_eq_tab_p7 (by decide) 28 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 7 tab_p7 chiD_eq_tab_p7 28 28 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_p7 : (List.range' 1 28).map (psi 7 28 28) = [1, 0, 1, 0, -1, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0] := by
  unfold psi
  rw [chiD_eq_tab_p7]
  decide

def tab_p9 : List ℤ := [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1]

theorem chiD_eq_tab_p9 : chiD 9 = fT tab_p9 :=
  chiD_eq_fT 9 (by norm_num) tab_p9 (by decide) (by
    intro m hm
    have hm' : m < 36 := hm
    interval_cases m <;> norm_num [chiD, tab_p9])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p9 : IsModulus 9 6 ∧ IsConductor 9 6 1 := by
  have hmod : IsModulus 9 6 :=
    isModulus_of_tab 9 tab_p9 chiD_eq_tab_p9 (by decide) 6 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 9 tab_p9 chiD_eq_tab_p9 6 1 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_p9 : (List.range' 1 1).map (psi 9 6 1) = [1] := by
  unfold psi
  rw [chiD_eq_tab_p9]
  decide

def tab_p10 : List ℤ := [0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 1]

theorem chiD_eq_tab_p10 : chiD 10 = fT tab_p10 :=
  chiD_eq_fT 10 (by norm_num) tab_p10 (by decide) (by
    intro m hm
    have hm' : m < 40 := hm
    interval_cases m <;> norm_num [chiD, tab_p10])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p10 : IsModulus 10 40 ∧ IsConductor 10 40 40 := by
  have hmod : IsModulus 10 40 :=
    isModulus_of_tab 10 tab_p10 chiD_eq_tab_p10 (by decide) 40 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 10 tab_p10 chiD_eq_tab_p10 40 40 hmod (by decide) (by decide) (by decide) (by decide)⟩

def tab_p11 : List ℤ := [0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1]

theorem chiD_eq_tab_p11 : chiD 11 = fT tab_p11 :=
  chiD_eq_fT 11 (by norm_num) tab_p11 (by decide) (by
    intro m hm
    have hm' : m < 44 := hm
    interval_cases m <;> norm_num [chiD, tab_p11])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_p11 : IsModulus 11 44 ∧ IsConductor 11 44 44 := by
  have hmod : IsModulus 11 44 :=
    isModulus_of_tab 11 tab_p11 chiD_eq_tab_p11 (by decide) 44 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab 11 tab_p11 chiD_eq_tab_p11 44 44 hmod (by decide) (by decide) (by decide) (by decide)⟩

def tab_n1 : List ℤ := [0, 1, 0, -1]

theorem chiD_eq_tab_n1 : chiD (-1) = fT tab_n1 :=
  chiD_eq_fT (-1) (by norm_num) tab_n1 (by decide) (by
    intro m hm
    have hm' : m < 4 := hm
    interval_cases m <;> norm_num [chiD, tab_n1])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n1 : IsModulus (-1) 4 ∧ IsConductor (-1) 4 4 := by
  have hmod : IsModulus (-1) 4 :=
    isModulus_of_tab (-1) tab_n1 chiD_eq_tab_n1 (by decide) 4 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-1) tab_n1 chiD_eq_tab_n1 4 4 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_n1 : (List.range' 1 4).map (psi (-1) 4 4) = [1, 0, -1, 0] := by
  unfold psi
  rw [chiD_eq_tab_n1]
  decide

def tab_n2 : List ℤ := [0, 1, 0, 1, 0, -1, 0, -1]

theorem chiD_eq_tab_n2 : chiD (-2) = fT tab_n2 :=
  chiD_eq_fT (-2) (by norm_num) tab_n2 (by decide) (by
    intro m hm
    have hm' : m < 8 := hm
    interval_cases m <;> norm_num [chiD, tab_n2])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n2 : IsModulus (-2) 8 ∧ IsConductor (-2) 8 8 := by
  have hmod : IsModulus (-2) 8 :=
    isModulus_of_tab (-2) tab_n2 chiD_eq_tab_n2 (by decide) 8 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-2) tab_n2 chiD_eq_tab_n2 8 8 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_n2 : (List.range' 1 8).map (psi (-2) 8 8) = [1, 0, 1, 0, -1, 0, -1, 0] := by
  unfold psi
  rw [chiD_eq_tab_n2]
  decide

def tab_n3 : List ℤ := [0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1]

theorem chiD_eq_tab_n3 : chiD (-3) = fT tab_n3 :=
  chiD_eq_fT (-3) (by norm_num) tab_n3 (by decide) (by
    intro m hm
    have hm' : m < 12 := hm
    interval_cases m <;> norm_num [chiD, tab_n3])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n3 : IsModulus (-3) 6 ∧ IsConductor (-3) 6 3 := by
  have hmod : IsModulus (-3) 6 :=
    isModulus_of_tab (-3) tab_n3 chiD_eq_tab_n3 (by decide) 6 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-3) tab_n3 chiD_eq_tab_n3 6 3 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_n3 : (List.range' 1 3).map (psi (-3) 6 3) = [1, -1, 0] := by
  unfold psi
  rw [chiD_eq_tab_n3]
  decide

def tab_n5 : List ℤ := [0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1]

theorem chiD_eq_tab_n5 : chiD (-5) = fT tab_n5 :=
  chiD_eq_fT (-5) (by norm_num) tab_n5 (by decide) (by
    intro m hm
    have hm' : m < 20 := hm
    interval_cases m <;> norm_num [chiD, tab_n5])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n5 : IsModulus (-5) 20 ∧ IsConductor (-5) 20 20 := by
  have hmod : IsModulus (-5) 20 :=
    isModulus_of_tab (-5) tab_n5 chiD_eq_tab_n5 (by decide) 20 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-5) tab_n5 chiD_eq_tab_n5 20 20 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_n5 : (List.range' 1 20).map (psi (-5) 20 20) = [1, 0, 1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0] := by
  unfold psi
  rw [chiD_eq_tab_n5]
  decide

def tab_n6 : List ℤ := [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1]

theorem chiD_eq_tab_n6 : chiD (-6) = fT tab_n6 :=
  chiD_eq_fT (-6) (by norm_num) tab_n6 (by decide) (by
    intro m hm
    have hm' : m < 24 := hm
    interval_cases m <;> norm_num [chiD, tab_n6])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n6 : IsModulus (-6) 24 ∧ IsConductor (-6) 24 24 := by
  have hmod : IsModulus (-6) 24 :=
    isModulus_of_tab (-6) tab_n6 chiD_eq_tab_n6 (by decide) 24 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-6) tab_n6 chiD_eq_tab_n6 24 24 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_n6 : (List.range' 1 24).map (psi (-6) 24 24) = [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0] := by
  unfold psi
  rw [chiD_eq_tab_n6]
  decide

def tab_n7 : List ℤ := [0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1]

theorem chiD_eq_tab_n7 : chiD (-7) = fT tab_n7 :=
  chiD_eq_fT (-7) (by norm_num) tab_n7 (by decide) (by
    intro m hm
    have hm' : m < 28 := hm
    interval_cases m <;> norm_num [chiD, tab_n7])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n7 : IsModulus (-7) 14 ∧ IsConductor (-7) 14 7 := by
  have hmod : IsModulus (-7) 14 :=
    isModulus_of_tab (-7) tab_n7 chiD_eq_tab_n7 (by decide) 14 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-7) tab_n7 chiD_eq_tab_n7 14 7 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_n7 : (List.range' 1 7).map (psi (-7) 14 7) = [1, 1, -1, 1, -1, -1, 0] := by
  unfold psi
  rw [chiD_eq_tab_n7]
  decide

def tab_n9 : List ℤ := [0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1]

theorem chiD_eq_tab_n9 : chiD (-9) = fT tab_n9 :=
  chiD_eq_fT (-9) (by norm_num) tab_n9 (by decide) (by
    intro m hm
    have hm' : m < 36 := hm
    interval_cases m <;> norm_num [chiD, tab_n9])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n9 : IsModulus (-9) 12 ∧ IsConductor (-9) 12 4 := by
  have hmod : IsModulus (-9) 12 :=
    isModulus_of_tab (-9) tab_n9 chiD_eq_tab_n9 (by decide) 12 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-9) tab_n9 chiD_eq_tab_n9 12 4 hmod (by decide) (by decide) (by decide) (by decide)⟩

@[kb "conwaysloane1988" "§8, Table 5, p. 269"]
theorem table5_n9 : (List.range' 1 4).map (psi (-9) 12 4) = [1, 0, -1, 0] := by
  unfold psi
  rw [chiD_eq_tab_n9]
  decide

def tab_n10 : List ℤ := [0, 1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1]

theorem chiD_eq_tab_n10 : chiD (-10) = fT tab_n10 :=
  chiD_eq_fT (-10) (by norm_num) tab_n10 (by decide) (by
    intro m hm
    have hm' : m < 40 := hm
    interval_cases m <;> norm_num [chiD, tab_n10])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n10 : IsModulus (-10) 40 ∧ IsConductor (-10) 40 40 := by
  have hmod : IsModulus (-10) 40 :=
    isModulus_of_tab (-10) tab_n10 chiD_eq_tab_n10 (by decide) 40 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-10) tab_n10 chiD_eq_tab_n10 40 40 hmod (by decide) (by decide) (by decide) (by decide)⟩

def tab_n11 : List ℤ := [0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1]

theorem chiD_eq_tab_n11 : chiD (-11) = fT tab_n11 :=
  chiD_eq_fT (-11) (by norm_num) tab_n11 (by decide) (by
    intro m hm
    have hm' : m < 44 := hm
    interval_cases m <;> norm_num [chiD, tab_n11])

@[kb "conwaysloane1988" "§8, Table 4, p. 269"]
theorem table4_n11 : IsModulus (-11) 22 ∧ IsConductor (-11) 22 11 := by
  have hmod : IsModulus (-11) 22 :=
    isModulus_of_tab (-11) tab_n11 chiD_eq_tab_n11 (by decide) 22 (by decide) (by decide) (by decide)
  exact ⟨hmod, isConductor_of_tab (-11) tab_n11 chiD_eq_tab_n11 22 11 hmod (by decide) (by decide) (by decide) (by decide)⟩

/-! ### (10): $\zeta_D$ in terms of the primitive L-series -/

/-- The completely multiplicative function $m \mapsto \psi(m)\,m^{-s}$ (real $s$). -/
noncomputable def mulRpow (ψ : ℕ →*₀ ℝ) (s : ℝ) : ℕ →*₀ ℝ where
  toFun n := ψ n * (n : ℝ) ^ (-s)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rw [ψ.map_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

theorem summable_mulRpow (ψ : ℕ →*₀ ℝ) (hψ : ∀ n, |ψ n| ≤ 1) {s : ℝ} (hs : 1 < s) :
    Summable (fun n => ‖mulRpow ψ s n‖) := by
  have hsm : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsm
  show ‖ψ n * (n : ℝ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (hψ n)

/-- The Euler factor at the primes dividing `k` (and `1` elsewhere). -/
noncomputable def badFactor (ψ : ℕ →*₀ ℝ) (k : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if n ∈ k.primeFactors then 1 - ψ n * (n : ℝ) ^ (-s) else 1

/-- **(10), p. 268**: for real $s > 1$,
$$\zeta_D(s) = L(s, \psi)\prod_{p \mid k}\bigl(1 - \psi(p)\,p^{-s}\bigr), \qquad L(s,\psi) = \sum_{m \ge 1}\psi(m)\,m^{-s},$$
where $k > 0$ is the modulus of $\chi_D$, $\psi$ is a completely multiplicative function with $\lvert\psi\rvert \le 1$ which agrees with
$\chi_D$ on integers coprime to $k$ (the primitive character $\psi$ of §8 has these properties), and $\chi_D(m) = 0$ when $m$ is
not coprime to $k$ ($\chi_D = \chi_1\psi$ with $\chi_1$ principal mod $k$). Proof: the Euler products (8) of both sides. -/
@[kb "conwaysloane1988" "§8 (10), p. 268"]
theorem zetaD_eq_L_mul {D : ℤ} (hD : D ≠ 0) {k : ℕ} (hk : 0 < k) (ψ : ℕ →*₀ ℝ) (hψ : ∀ n, |ψ n| ≤ 1)
    (hag : ∀ m, Nat.Coprime m k → (ψ m : ℝ) = chiD D m)
    (hz : ∀ m, ¬ Nat.Coprime m k → chiD D m = 0) {s : ℝ} (hs : 1 < s) :
    zetaD D s = (∑' m : ℕ, ψ m * (m : ℝ) ^ (-s)) * ∏ p ∈ k.primeFactors, (1 - ψ p * (p : ℝ) ^ (-s)) := by
  have hE1 := eulerProduct_zetaD hD hs
  have hE2 := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_mulRpow ψ hψ hs)
  have hG := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional Nat.Primes) (f := fun p : Nat.Primes => badFactor ψ k s p.1)
    (s := k.primeFactors.subtype Nat.Prime) (by
      intro p hp
      have : (p : ℕ) ∉ k.primeFactors := by
        intro h
        exact hp (Finset.mem_subtype.2 h)
      simp [badFactor, this])
  have hmul := hE2.mul hG
  have hpos : ∀ p : Nat.Primes, 0 < (1 - ψ p * (p : ℝ) ^ (-s)) := by
    intro p
    have h2 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    have h3 : (p : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg h2 (by linarith)
    have h4 : |ψ p * (p : ℝ) ^ (-s)| < 1 := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      calc |ψ p| * (p : ℝ) ^ (-s) ≤ 1 * (p : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_right (hψ p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ < 1 := by linarith
    linarith [(abs_lt.1 h4).2]
  have heq : (fun p : Nat.Primes => (1 - mulRpow ψ s p)⁻¹ * badFactor ψ k s p.1)
      = fun p : Nat.Primes => (1 - (chiD D p : ℝ) * (p : ℝ) ^ (-s))⁻¹ := by
    funext p
    by_cases hp : (p : ℕ) ∣ k
    · have hmem : (p : ℕ) ∈ k.primeFactors := Nat.mem_primeFactors.2 ⟨p.2, hp, hk.ne'⟩
      have hnc : ¬ Nat.Coprime p k := by
        rw [Nat.Prime.coprime_iff_not_dvd p.2]; exact not_not.2 hp
      rw [hz p hnc]
      simp only [badFactor, if_pos hmem]
      show (1 - ψ p * (p : ℝ) ^ (-s))⁻¹ * (1 - ψ p * (p : ℝ) ^ (-s)) = _
      rw [inv_mul_cancel₀ (hpos p).ne']
      simp
    · have hnmem : (p : ℕ) ∉ k.primeFactors := fun h => hp (Nat.dvd_of_mem_primeFactors h)
      have hc : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd p.2).2 hp
      simp only [badFactor, if_neg hnmem, mul_one]
      show (1 - ψ p * (p : ℝ) ^ (-s))⁻¹ = _
      rw [hag p hc]
  rw [heq] at hmul
  have hu := hE1.unique hmul
  rw [hu]
  have h1 : ∏ b ∈ k.primeFactors.subtype Nat.Prime, badFactor ψ k s (b : ℕ)
      = ∏ p ∈ k.primeFactors, (1 - ψ p * (p : ℝ) ^ (-s)) := by
    rw [Finset.prod_subtype_eq_prod_filter,
      Finset.filter_true_of_mem (fun p hp => (Nat.prime_of_mem_primeFactors hp))]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    simp [badFactor, hp]
  congr 1

/-! ### Table 6: $\zeta_{-1}(1) = \pi/4$ -/

open Filter Topology Finset in
/-- The Dirichlet character modulo $4$ attached to $\chi_{-1}$ (Mathlib's `ZMod.χ₄` with values in $\mathbb C$). -/
noncomputable def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chi4_apply (n : ℕ) : chi4 (n : ZMod 4) = (chiD (-1) n : ℂ) := by
  unfold chiD chi4
  rw [MulChar.ringHomComp_apply]
  split_ifs with h
  · rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos h]; simp
  · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
    rw [jacobiSym.at_neg_one hodd]
    simp

theorem chi4_ne_one : chi4 ≠ 1 := by
  intro h
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  have e : ((3 : ℕ) : ZMod 4) = 3 := by norm_num
  rw [← e, chi4_apply, MulChar.one_apply (by decide)] at h3
  norm_num [chiD] at h3

theorem LFunction_cast {N M : ℕ} [NeZero N] [NeZero M] (h : N = M) (Φ : ZMod N → ℂ) (Ψ : ZMod M → ℂ)
    (hΦΨ : ∀ n : ℕ, Φ (n : ZMod N) = Ψ (n : ZMod M)) : ZMod.LFunction Φ = ZMod.LFunction Ψ := by
  subst h
  have : Φ = Ψ := by
    funext x
    have e : ((x.val : ℕ) : ZMod N) = x := ZMod.natCast_zmod_val x
    rw [← e]
    exact hΦΨ _
  rw [this]

theorem LD_neg_one (h : (-1 : ℤ) ≠ 0) (s : ℂ) : LD (-1) h s = chi4.LFunction s := by
  haveI := neZero_four_natAbs h
  unfold LD
  have := LFunction_cast (N := 4 * (-1 : ℤ).natAbs) (M := 4) (by norm_num) (Phi (-1))
    (fun x => chi4 x) (fun n => by rw [Phi_natCast, chi4_apply])
  rw [this]
  rfl

open Filter Topology Finset QuadFormsKB.Binary.EulerOne in
/-- **Table 6, $d = 1$, $s = 1$ (via (9), (14)):** $\zeta_{-1}(1) = 1 - \tfrac13 + \tfrac15 - \tfrac17 + \cdots = \pi/4$
(Leibniz' series, identified with Mathlib's analytic continuation at $s = 1$ through the error bound of `EulerProductAtOne`). -/
@[kb "conwaysloane1988" "§8, Table 6, p. 270 (d = 1, s = 1)"]
theorem zetaD_neg_one_one : zetaD (-1) 1 = π / 4 := by
  have h : (-1 : ℤ) ≠ 0 := by norm_num
  rw [zetaD_eq h, LD_neg_one h, Complex.ofReal_one]
  -- partial sums
  have hpart : ∀ k : ℕ, lpart chi4 (2 * k) 1
      = (((∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1) : ℝ)) : ℂ) := by
    intro k
    induction k with
    | zero => simp [lpart]
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      unfold lpart at *
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have e0 : chi4 ((2 * k : ℕ) : ZMod 4) = 0 := by
        rw [chi4_apply]; simp [chiD]
      have e1 : chi4 ((2 * k + 1 : ℕ) : ZMod 4) = (-1 : ℂ) ^ k := by
        rw [chi4_apply]
        have : chiD (-1) (2 * k + 1) = (-1) ^ k := by
          unfold chiD
          rw [if_neg (by omega), jacobiSym.at_neg_one (by simp), ZMod.χ₄_eq_neg_one_pow (by omega)]
          congr 2
          omega
        rw [this]; push_cast; rfl
      have hw : wpow 1 (2 * k + 1) = 1 / (2 * (k : ℝ) + 1) := by
        unfold wpow
        rw [if_neg (by omega), Real.rpow_neg_one]
        push_cast
        ring
      rw [e0, e1, hw]
      push_cast
      ring
  have h1 : Tendsto (fun k : ℕ => lpart chi4 (2 * k) 1) atTop (𝓝 (chi4.LFunction 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (g := fun k : ℕ => 4 * (4 : ℝ) / ((2 * k : ℕ) + 1)) ?_
    · have := norm_lpart_one_sub_LFunction_le chi4 chi4_ne_one (2 * k)
      simpa using this
    · have : Tendsto (fun k : ℕ => (4 : ℝ) * 4 / (((2 * k : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact tendsto_atTop_mono (fun k => by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
          tendsto_natCast_atTop_atTop
      exact this
  have h2 : Tendsto (fun k : ℕ => lpart chi4 (2 * k) 1) atTop (𝓝 ((π / 4 : ℝ) : ℂ)) := by
    simp_rw [hpart]
    exact (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_sum_pi_div_four
  have := tendsto_nhds_unique h1 h2
  rw [this]
  simp


end QuadFormsKB.ConwaySloane.Mass
