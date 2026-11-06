/-
# Gan–Hanke–Yu 2001: the local factor (2.12) and the λ columns of Tables 1–4, (8.6), (8.10)

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), (2.12), p. 104;
Tables 1–2 (pp. 106–107), Tables 3–4 (pp. 115–116), (8.5)–(8.6), (8.9)–(8.10) (pp. 120–121).

GHY's local factor at a finite place $v$ with residue field $\mathbb F_q$ is the volume ratio (2.12)
$$\lambda_v = \frac{q^{-N(\overline H{}^0)}\,\#\overline H{}^0(\mathbb F_q)}{q^{-N(\overline G)}\,\#\overline G(\mathbb F_q)},$$
where $\overline G$ is the maximal reductive quotient of the special fibre of the Bruhat–Tits model of the stabilizer of a maximal
lattice, $\overline H{}^0$ the same for the quasi-split inner form's special model, and $N(\cdot)$ the number of positive roots
over $\overline{\mathbb F}_q$. The tables list $\overline G$, $\overline H{}^0$ and the resulting $\lambda$.

Here the finite reductive groups occurring in the tables are an inductive type `RedGrp`; each carries its order as a function
of $q$ (`RedGrp.card`, the standard orders of the finite classical groups, e.g. Carter, *Finite groups of Lie type*, §2.9;
Artin, *Geometric algebra*, Ch. III–V) and $N$ (`RedGrp.numPos`). The volume $q^{-N}\#(\cdot)$ is `RedGrp.vol` and (2.12) is
`lam`. **Every $\lambda$ entry of Tables 1–4, (8.6) and (8.10) is then proved** from (2.12) (`table1_row2`, …, `eq8_10`).

The groups (GHY's notation, p. 106–107): $GL_m$, $U_m$ (unitary, split by $\mathbb F_{q^2}$), $Sp_{2n}$, $SO_{2n+1}$,
$SO_{2n}$ / ${}^2SO_{2n}$ (split / quasi-split nonsplit), $O_{2n}$ / ${}^2O_{2n}$, $\mathrm{Res}_{\mathbb F_{q^2}/\mathbb F_q}Sp_{2n}$,
$\mathbb Z/2\mathbb Z$, products, and the index-2 subgroups $S(O\times O')$ of Table 3. Orders:
$\#GL_m = q^{\binom m2}\prod_{i=1}^m(q^i-1)$, $\#U_m = q^{\binom m2}\prod_{i=1}^m(q^i-(-1)^i)$,
$\#Sp_{2n} = \#SO_{2n+1} = q^{n^2}\prod_{i=1}^n(q^{2i}-1)$, $\#SO^{\pm}_{2n} = q^{n(n-1)}(q^n\mp1)\prod_{i=1}^{n-1}(q^{2i}-1)$ ($n\ge1$),
$\#O^\pm_{2n} = 2\,\#SO^\pm_{2n}$, $\#\mathrm{Res}\,Sp_{2n}(\mathbb F_q) = \#Sp_{2n}(\mathbb F_{q^2})$.

Also: the local types of the unitary (Tables 1–2) and quaternionic ((8.5), (8.9)) cases as functions of the local data
(`unitaryGbar`, `unitaryHbar`, `quatGbar`, `quatIntGbar`), and the local factors of Propositions 4.4, 4.5, 9.3, 9.4 as
printed (`lambdaProp44`, …), proved equal to (2.12) for these types (`lam_unitary_odd`, …). Indices are 0-based where
they index products: $\prod_{i=1}^m$ is `∏ i ∈ Finset.range m` with `i + 1`.
-/
import Mathlib
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.GanHankeYu2001

open Finset

/-- **The finite reductive groups over $\mathbb F_q$ in GHY's tables** (GHY 2001, notation of pp. 106–107, 115):
`GL m` $= GL_m$; `U m` $= U_m$ (unitary group in $m$ variables, split by $\mathbb F_{q^2}$); `Sp n` $= Sp_{2n}$;
`SOodd n` $= SO_{2n+1}$; `SOplus n` $= SO_{2n}$ (split); `SOminus n` $= {}^2SO_{2n}$ (quasi-split, nonsplit); `Oplus n` $= O_{2n}$;
`Ominus n` $= {}^2O_{2n}$; `resSp n` $= \mathrm{Res}_{\mathbb F_{q^2}/\mathbb F_q}Sp_{2n}$; `Z2` $= \mathbb Z/2\mathbb Z$; `prod G H` $= G\times H$;
`sKer G` = the index-2 subgroup $S(\cdots)$, the kernel of the product of the Dickson / determinant maps (Table 3). -/
@[kb "ganhankeyu2001" "§3, p. 106 (notation for Tables 1–4)"]
inductive RedGrp
  | GL (m : ℕ)
  | U (m : ℕ)
  | Sp (n : ℕ)
  | SOodd (n : ℕ)
  | SOplus (n : ℕ)
  | SOminus (n : ℕ)
  | Oplus (n : ℕ)
  | Ominus (n : ℕ)
  | resSp (n : ℕ)
  | Z2
  | prod (G H : RedGrp)
  | sKer (G : RedGrp)
  deriving DecidableEq

/-- $\prod_{i=1}^n(q^{2i}-1)$. -/
def spProd (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1)

/-- $\prod_{i=1}^m(q^i-(-1)^i)$, the unipotent-free part of $\#U_m(\mathbb F_q)$. -/
def uProd (q : ℝ) (m : ℕ) : ℝ := ∏ i ∈ range m, (q ^ (i + 1) - (-1) ^ (i + 1))

/-- $\prod_{i=1}^m(q^i-1)$, the unipotent-free part of $\#GL_m(\mathbb F_q)$. -/
def glProd (q : ℝ) (m : ℕ) : ℝ := ∏ i ∈ range m, (q ^ (i + 1) - 1)

/-- $q^{-N}\#\overline G(\mathbb F_q)$ for $\overline G$ a special orthogonal group of type $\pm$ in $2n$ variables:
$(q^n\mp1)\prod_{i=1}^{n-1}(q^{2i}-1)$ for $n\ge1$, and $1$ for $n = 0$. -/
def soEvenProd (q : ℝ) (ε : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else (q ^ n - ε) * spProd q (n - 1)

namespace RedGrp

/-- **$N(\overline G)$, the number of positive roots over $\overline{\mathbb F}_q$** (GHY 2001, (2.7)). -/
@[kb "ganhankeyu2001" "(2.7), p. 104 (N(G), number of positive roots)"]
def numPos : RedGrp → ℕ
  | .GL m => m * (m - 1) / 2
  | .U m => m * (m - 1) / 2
  | .Sp n => n ^ 2
  | .SOodd n => n ^ 2
  | .SOplus n => n * (n - 1)
  | .SOminus n => n * (n - 1)
  | .Oplus n => n * (n - 1)
  | .Ominus n => n * (n - 1)
  | .resSp n => 2 * n ^ 2
  | .Z2 => 0
  | .prod G H => numPos G + numPos H
  | .sKer G => numPos G

/-- **$q^{-N(\overline G)}\#\overline G(\mathbb F_q)$** (GHY 2001, (2.12)), with the standard orders of the finite classical
groups (module docstring). Equivalently `card G q = q ^ numPos G * vol G q` (`card`). -/
@[kb "ganhankeyu2001" "(2.12), p. 104 (q^{-N(G)}·#G(F_q))"]
def vol (q : ℝ) : RedGrp → ℝ
  | .GL m => glProd q m
  | .U m => uProd q m
  | .Sp n => spProd q n
  | .SOodd n => spProd q n
  | .SOplus n => soEvenProd q 1 n
  | .SOminus n => soEvenProd q (-1) n
  | .Oplus n => (if n = 0 then 1 else 2) * soEvenProd q 1 n
  | .Ominus n => (if n = 0 then 1 else 2) * soEvenProd q (-1) n
  | .resSp n => spProd (q ^ 2) n
  | .Z2 => 2
  | .prod G H => vol q G * vol q H
  | .sKer G => vol q G / 2

/-- **$\#\overline G(\mathbb F_q)$**, the order of the finite group. -/
def card (G : RedGrp) (q : ℝ) : ℝ := q ^ numPos G * vol q G

end RedGrp

open RedGrp

/-- **GHY's local factor (2.12)**: $\lambda = \dfrac{q^{-N(\overline H{}^0)}\#\overline H{}^0(\mathbb F_q)}{q^{-N(\overline G)}\#\overline G(\mathbb F_q)}$. -/
@[kb "ganhankeyu2001" "(2.12), p. 104"]
def lam (H G : RedGrp) (q : ℝ) : ℝ := vol q H / vol q G

/-- (2.12) as printed, with the powers of $q$ written out: $\lambda = q^{-N(\overline H{}^0)}\#\overline H{}^0/(q^{-N(\overline G)}\#\overline G)$. -/
theorem lam_eq_card (H G : RedGrp) {q : ℝ} (hq : q ≠ 0) :
    lam H G q = (q ^ numPos H)⁻¹ * H.card q / ((q ^ numPos G)⁻¹ * G.card q) := by
  simp only [lam, RedGrp.card]
  have h1 : (q ^ numPos H) ≠ 0 := pow_ne_zero _ hq
  have h2 : (q ^ numPos G) ≠ 0 := pow_ne_zero _ hq
  rw [inv_mul_cancel_left₀ h1, inv_mul_cancel_left₀ h2]

/-! ### Positivity -/

section Pos

variable {q : ℝ}

theorem spProd_pos (hq : 1 < q) (n : ℕ) : 0 < spProd q n :=
  prod_pos fun i _ => by
    have : 1 < q ^ (2 * (i + 1)) := one_lt_pow₀ hq (by omega)
    linarith

theorem glProd_pos (hq : 1 < q) (m : ℕ) : 0 < glProd q m :=
  prod_pos fun i _ => by
    have : 1 < q ^ (i + 1) := one_lt_pow₀ hq (by omega)
    linarith

theorem uProd_pos (hq : 1 < q) (m : ℕ) : 0 < uProd q m :=
  prod_pos fun i _ => by
    have : 1 < q ^ (i + 1) := one_lt_pow₀ hq (by omega)
    rcases neg_one_pow_eq_or ℝ (i + 1) with h | h <;> rw [h] <;> linarith

theorem soEvenProd_pos (hq : 1 < q) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (n : ℕ) : 0 < soEvenProd q ε n := by
  unfold soEvenProd
  split_ifs with h
  · exact one_pos
  · refine mul_pos ?_ (spProd_pos hq _)
    have : 1 < q ^ n := one_lt_pow₀ hq h
    rcases hε with rfl | rfl <;> linarith

theorem vol_pos (hq : 1 < q) : ∀ G : RedGrp, 0 < vol q G
  | .GL m => glProd_pos hq m
  | .U m => uProd_pos hq m
  | .Sp n => spProd_pos hq n
  | .SOodd n => spProd_pos hq n
  | .SOplus n => soEvenProd_pos hq (Or.inl rfl) n
  | .SOminus n => soEvenProd_pos hq (Or.inr rfl) n
  | .Oplus n => mul_pos (by split_ifs <;> norm_num) (soEvenProd_pos hq (Or.inl rfl) n)
  | .Ominus n => mul_pos (by split_ifs <;> norm_num) (soEvenProd_pos hq (Or.inr rfl) n)
  | .resSp n => spProd_pos (one_lt_pow₀ hq (by norm_num)) n
  | .Z2 => two_pos
  | .prod G H => mul_pos (vol_pos hq G) (vol_pos hq H)
  | .sKer G => div_pos (vol_pos hq G) two_pos

theorem lam_self (hq : 1 < q) (G : RedGrp) : lam G G q = 1 := div_self (vol_pos hq G).ne'

end Pos

/-! ### Product identities -/

section Prod

variable (q : ℝ)

theorem spProd_succ (n : ℕ) : spProd q (n + 1) = spProd q n * (q ^ (2 * (n + 1)) - 1) := prod_range_succ _ _

theorem uProd_succ (m : ℕ) : uProd q (m + 1) = uProd q m * (q ^ (m + 1) - (-1) ^ (m + 1)) := prod_range_succ _ _

/-- $\prod_{i=1}^{m}(q^{2i}-1) = \prod_{i=1}^m(q^i-(-1)^i)\cdot\prod_{i=1}^m(q^i+(-1)^i)$. -/
theorem spProd_eq_uProd_mul (m : ℕ) :
    spProd q m = uProd q m * ∏ i ∈ range m, (q ^ (i + 1) + (-1) ^ (i + 1)) := by
  induction m with
  | zero => simp [spProd, uProd]
  | succ m ih =>
    rw [spProd_succ, uProd_succ, prod_range_succ, ih]
    have : ((-1 : ℝ) ^ (m + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    have e : q ^ (2 * (m + 1)) - 1 = (q ^ (m + 1) - (-1) ^ (m + 1)) * (q ^ (m + 1) + (-1) ^ (m + 1)) := by
      rw [show q ^ (2 * (m + 1)) = (q ^ (m + 1)) ^ 2 by rw [← pow_mul, mul_comm]]
      nlinarith [this]
    rw [e]; ring

/-- $\prod_{i=1}^{2n}(q^{2i}-1) = \prod_{r=1}^n(q^{4r-2}-1)\cdot\prod_{i=1}^n((q^2)^{2i}-1)$. -/
theorem spProd_two_mul (n : ℕ) :
    spProd q (2 * n) = (∏ r ∈ range n, (q ^ (4 * (r + 1) - 2) - 1)) * spProd (q ^ 2) n := by
  induction n with
  | zero => simp [spProd]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, spProd_succ, spProd_succ, ih, spProd_succ, prod_range_succ]
    rw [show 4 * (n + 1) - 2 = 2 * (2 * n + 1) by omega, ← pow_mul,
      show 2 * (2 * (n + 1)) = 2 * (2 * n + 1 + 1) by ring]
    ring

end Prod

/-! ### Unfolding lemmas for `vol` -/

section VolLemmas

variable (q : ℝ)

@[simp] theorem vol_prod (G H : RedGrp) : vol q (.prod G H) = vol q G * vol q H := rfl
@[simp] theorem vol_sKer (G : RedGrp) : vol q (.sKer G) = vol q G / 2 := rfl
@[simp] theorem vol_Z2 : vol q .Z2 = 2 := rfl
@[simp] theorem vol_U (m : ℕ) : vol q (.U m) = uProd q m := rfl
@[simp] theorem vol_GL (m : ℕ) : vol q (.GL m) = glProd q m := rfl
@[simp] theorem vol_Sp (n : ℕ) : vol q (.Sp n) = spProd q n := rfl
@[simp] theorem vol_SOodd (n : ℕ) : vol q (.SOodd n) = spProd q n := rfl
@[simp] theorem vol_resSp (n : ℕ) : vol q (.resSp n) = spProd (q ^ 2) n := rfl

theorem vol_SOplus_succ (n : ℕ) : vol q (.SOplus (n + 1)) = (q ^ (n + 1) - 1) * spProd q n := by
  simp [vol, soEvenProd]

theorem vol_SOminus_succ (n : ℕ) : vol q (.SOminus (n + 1)) = (q ^ (n + 1) + 1) * spProd q n := by
  simp [vol, soEvenProd]

theorem vol_Oplus_succ (n : ℕ) : vol q (.Oplus (n + 1)) = 2 * ((q ^ (n + 1) - 1) * spProd q n) := by
  simp [vol, soEvenProd]

theorem vol_Ominus_succ (n : ℕ) : vol q (.Ominus (n + 1)) = 2 * ((q ^ (n + 1) + 1) * spProd q n) := by
  simp [vol, soEvenProd]

theorem spProd_zero : spProd q 0 = 1 := by simp [spProd]

theorem uProd_one : uProd q 1 = q + 1 := by simp [uProd]

theorem vol_Ominus_one : vol q (.Ominus 1) = 2 * (q + 1) := by
  rw [vol_Ominus_succ, spProd_zero]; ring

end VolLemmas

/-! ### Table 1: odd unitary groups, $m = 2n+1$ (GHY p. 106) -/

section Tables

variable {q : ℝ}

/-- **Table 1, row 2** ($E$ unramified, $\alpha\notin A^\times$): $\overline G = U_{2n}\times U_1$, $\overline H{}^0 = U_{2n+1}$,
$\lambda = (q^{2n+1}+1)/(q+1)$. -/
@[kb "ganhankeyu2001" "Table 1, row 2, p. 106"]
theorem table1_row2 (hq : 1 < q) (n : ℕ) :
    lam (.U (2 * n + 1)) (.prod (.U (2 * n)) (.U 1)) q = (q ^ (2 * n + 1) + 1) / (q + 1) := by
  have hP := (uProd_pos hq (2 * n)).ne'
  have hq1 : q + 1 ≠ 0 := by linarith
  have e : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_pow ⟨n, rfl⟩
  rw [lam, vol_prod, vol_U, vol_U, vol_U, uProd_one, uProd_succ, e]
  field_simp
  ring

/-- **Table 1, row 3** ($E$ ramified): $\overline G = \mathbb Z/2\times Sp_{2n}$, $\overline H{}^0 = SO_{2n+1}$, $\lambda = 1/2$. -/
@[kb "ganhankeyu2001" "Table 1, row 3, p. 106"]
theorem table1_row3 (hq : 1 < q) (n : ℕ) : lam (.SOodd n) (.prod .Z2 (.Sp n)) q = 1 / 2 := by
  have hP := (spProd_pos hq n).ne'
  rw [lam, vol_prod, vol_SOodd, vol_Z2, vol_Sp]
  field_simp

/-! ### Table 2: even unitary groups, $m = 2n$ (GHY p. 107) -/

/-- **Table 2, row 2** ($E$ unramified, $\alpha\notin NE^\times$): $\overline G = U_{2n-1}\times U_1$, $\overline H{}^0 = U_{2n}$,
$\lambda = (q^{2n}-1)/(q+1)$ ($n\ge1$). -/
@[kb "ganhankeyu2001" "Table 2, row 2, p. 107"]
theorem table2_row2 (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n) :
    lam (.U (2 * n)) (.prod (.U (2 * n - 1)) (.U 1)) q = (q ^ (2 * n) - 1) / (q + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hP := (uProd_pos hq (2 * k + 1)).ne'
  have hq1 : q + 1 ≠ 0 := by linarith
  have e : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := Even.neg_one_pow ⟨k + 1, by ring⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
  rw [lam, vol_prod, vol_U, vol_U, vol_U, uProd_one, uProd_succ, e]
  field_simp

/-- **Table 2, row 4** ($E$ ramified, $\alpha\notin NE^\times$): $\overline G = Sp_{2n-2}\times{}^2O_2$, $\overline H{}^0 = Sp_{2n}$,
$\lambda = \frac12(q^{2n}-1)/(q+1)$ ($n\ge1$). -/
@[kb "ganhankeyu2001" "Table 2, row 4, p. 107"]
theorem table2_row4 (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n) :
    lam (.Sp n) (.prod (.Sp (n - 1)) (.Ominus 1)) q = 1 / 2 * ((q ^ (2 * n) - 1) / (q + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hP := (spProd_pos hq k).ne'
  have hq1 : q + 1 ≠ 0 := by linarith
  rw [Nat.add_sub_cancel, lam, vol_prod, vol_Sp, vol_Sp, vol_Ominus_one, spProd_succ]
  field_simp

/-! ### Table 3: even special orthogonal groups, $m = 2n$, $n\ge2$ (GHY p. 115) -/

/-- **Table 3, row 2** ($\delta\in F^{\times2}$, $w = -1$): $\overline G = S({}^2O_{2n-2}\times{}^2O_2)$, $\overline H{}^0 = SO_{2n}$,
$\lambda = (q^{n-1}-1)(q^n-1)/(2(q+1))$. -/
@[kb "ganhankeyu2001" "Table 3, row 2, p. 115"]
theorem table3_row2 (hq : 1 < q) {n : ℕ} (hn : 2 ≤ n) :
    lam (.SOplus n) (.sKer (.prod (.Ominus (n - 1)) (.Ominus 1))) q =
      (q ^ (n - 1) - 1) * (q ^ n - 1) / (2 * (q + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have hP := (spProd_pos hq k).ne'
  have hq1 : q + 1 ≠ 0 := by linarith
  have hq2 : q ^ (k + 1) + 1 ≠ 0 := by have := pow_pos (by linarith : (0 : ℝ) < q) (k + 1); linarith
  rw [Nat.add_sub_cancel, lam, vol_sKer, vol_prod, vol_SOplus_succ, vol_Ominus_succ, vol_Ominus_one, spProd_succ]
  have e : q ^ (2 * (k + 1)) - 1 = (q ^ (k + 1) - 1) * (q ^ (k + 1) + 1) := by
    rw [mul_comm, pow_mul]; ring
  rw [e]
  field_simp

/-- **Table 3, row 4** ($\delta\notin F^{\times2}$, $E_\delta$ unramified, $w = -1$): $\overline G = S(O_{2n-2}\times{}^2O_2)$,
$\overline H{}^0 = {}^2SO_{2n}$, $\lambda = (q^{n-1}+1)(q^n+1)/(2(q+1))$. -/
@[kb "ganhankeyu2001" "Table 3, row 4, p. 115"]
theorem table3_row4 (hq : 1 < q) {n : ℕ} (hn : 2 ≤ n) :
    lam (.SOminus n) (.sKer (.prod (.Oplus (n - 1)) (.Ominus 1))) q =
      (q ^ (n - 1) + 1) * (q ^ n + 1) / (2 * (q + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have hP := (spProd_pos hq k).ne'
  have hq1 : q + 1 ≠ 0 := by linarith
  have hq2 : q ^ (k + 1) - 1 ≠ 0 := by have := one_lt_pow₀ hq (show k + 1 ≠ 0 by omega); linarith
  rw [Nat.add_sub_cancel, lam, vol_sKer, vol_prod, vol_SOminus_succ, vol_Oplus_succ, vol_Ominus_one, spProd_succ]
  have e : q ^ (2 * (k + 1)) - 1 = (q ^ (k + 1) - 1) * (q ^ (k + 1) + 1) := by
    rw [mul_comm, pow_mul]; ring
  rw [e]
  field_simp

/-- **Table 3, row 5** ($E_\delta$ ramified): $\overline G = \mathbb Z/2\times SO_{2n-1}$, $\overline H{}^0 = SO_{2n-1}$, $\lambda = 1/2$. -/
@[kb "ganhankeyu2001" "Table 3, row 5, p. 115"]
theorem table3_row5 (hq : 1 < q) (n : ℕ) : lam (.SOodd (n - 1)) (.prod .Z2 (.SOodd (n - 1))) q = 1 / 2 := by
  have hP := (spProd_pos hq (n - 1)).ne'
  rw [lam, vol_prod, vol_SOodd, vol_Z2]
  field_simp

/-! ### Table 4: odd special orthogonal groups, $m = 2n+1$ (GHY p. 116) -/

/-- **Table 4, row 2** ($\delta\notin A^\times$, $w = 1$): $\overline G = O_{2n}$, $\overline H{}^0 = SO_{2n+1}$, $\lambda = (q^n+1)/2$
($n\ge1$). -/
@[kb "ganhankeyu2001" "Table 4, row 2, p. 116"]
theorem table4_row2 (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n) : lam (.SOodd n) (.Oplus n) q = (q ^ n + 1) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hP := (spProd_pos hq k).ne'
  have hq2 : q ^ (k + 1) - 1 ≠ 0 := by have := one_lt_pow₀ hq (show k + 1 ≠ 0 by omega); linarith
  rw [lam, vol_SOodd, vol_Oplus_succ, spProd_succ]
  have e : q ^ (2 * (k + 1)) - 1 = (q ^ (k + 1) - 1) * (q ^ (k + 1) + 1) := by
    rw [mul_comm, pow_mul]; ring
  rw [e]
  field_simp

/-- **Table 4, row 3** ($\delta\in A^\times$, $w = -1$): $\overline G = SO_{2n-1}\times{}^2O_2$, $\overline H{}^0 = SO_{2n+1}$,
$\lambda = (q^{2n}-1)/(2(q+1))$ ($n\ge1$). -/
@[kb "ganhankeyu2001" "Table 4, row 3, p. 116"]
theorem table4_row3 (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n) :
    lam (.SOodd n) (.prod (.SOodd (n - 1)) (.Ominus 1)) q = (q ^ (2 * n) - 1) / (2 * (q + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hP := (spProd_pos hq k).ne'
  have hq1 : q + 1 ≠ 0 := by linarith
  rw [Nat.add_sub_cancel, lam, vol_prod, vol_SOodd, vol_SOodd, vol_Ominus_one, spProd_succ]
  field_simp

/-- **Table 4, row 4** ($\delta\notin A^\times$, $w = -1$): $\overline G = {}^2O_{2n}$, $\overline H{}^0 = SO_{2n+1}$, $\lambda = (q^n-1)/2$
($n\ge1$). -/
@[kb "ganhankeyu2001" "Table 4, row 4, p. 116"]
theorem table4_row4 (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n) : lam (.SOodd n) (.Ominus n) q = (q ^ n - 1) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hP := (spProd_pos hq k).ne'
  have hq2 : q ^ (k + 1) + 1 ≠ 0 := by have := pow_pos (by linarith : (0 : ℝ) < q) (k + 1); linarith
  rw [lam, vol_SOodd, vol_Ominus_succ, spProd_succ]
  have e : q ^ (2 * (k + 1)) - 1 = (q ^ (k + 1) - 1) * (q ^ (k + 1) + 1) := by
    rw [mul_comm, pow_mul]; ring
  rw [e]
  field_simp

/-! ### Quaternionic hermitian spaces: (8.6) and (8.10) (GHY pp. 120–121) -/

/-- **(8.6), $m = 2n$**: $\overline G = \mathrm{Res}_{\mathbb F_{q^2}/\mathbb F_q}Sp_{2n}$, $\overline H{}^0 = Sp_{4n}$:
$\lambda = \prod_{r=1}^n(q^{4r-2}-1)$. -/
@[kb "ganhankeyu2001" "(8.5)–(8.6), m = 2n, pp. 120–121"]
theorem eq8_6_even (hq : 1 < q) (n : ℕ) :
    lam (.Sp (2 * n)) (.resSp n) q = ∏ r ∈ range n, (q ^ (4 * (r + 1) - 2) - 1) := by
  have hP := (spProd_pos (one_lt_pow₀ hq (by norm_num : (2 : ℕ) ≠ 0)) n).ne'
  rw [lam, vol_Sp, vol_resSp, spProd_two_mul]
  field_simp

/-- **(8.6), $m = 2n+1$**: $\overline G = \mathrm{Res}_{\mathbb F_{q^2}/\mathbb F_q}Sp_{2n}\times U_1$, $\overline H{}^0 = Sp_{4n+2}$:
$\lambda = \prod_{r=1}^n(q^{4r-2}-1)\cdot(q^{4n+2}-1)/(q+1)$. -/
@[kb "ganhankeyu2001" "(8.5)–(8.6), m = 2n + 1, pp. 120–121"]
theorem eq8_6_odd (hq : 1 < q) (n : ℕ) :
    lam (.Sp (2 * n + 1)) (.prod (.resSp n) (.U 1)) q =
      (∏ r ∈ range n, (q ^ (4 * (r + 1) - 2) - 1)) * ((q ^ (4 * n + 2) - 1) / (q + 1)) := by
  have hP := (spProd_pos (one_lt_pow₀ hq (by norm_num : (2 : ℕ) ≠ 0)) n).ne'
  have hq1 : q + 1 ≠ 0 := by linarith
  rw [lam, vol_Sp, vol_prod, vol_resSp, vol_U, uProd_one, spProd_succ, spProd_two_mul,
    show 2 * (2 * n + 1) = 4 * n + 2 by ring]
  field_simp

/-- **(8.10)**: for the maximal integral lattice, $\overline G = U_m$, $\overline H{}^0 = Sp_{2m}$:
$\lambda = \prod_{r=1}^m(q^r+(-1)^r)$. -/
@[kb "ganhankeyu2001" "(8.9)–(8.10), p. 121"]
theorem eq8_10 (hq : 1 < q) (m : ℕ) : lam (.Sp m) (.U m) q = ∏ r ∈ range m, (q ^ (r + 1) + (-1) ^ (r + 1)) := by
  have hP := (uProd_pos hq m).ne'
  rw [lam, vol_Sp, vol_U, spProd_eq_uProd_mul]
  field_simp

end Tables

/-! ### The local types of the unitary and quaternionic cases, and the printed local factors of §§4, 9 -/

/-- **How a finite place $v$ of $k$ behaves in the quadratic extension $L/k$** (GHY 2001, §4: $L_v = L\otimes_kk_v$ is
$k_v\times k_v$, an unramified, or a ramified quadratic extension). -/
@[kb "ganhankeyu2001" "§4, p. 109 (L_v split, unramified or ramified)"]
inductive LocalExt
  | split
  | inert
  | ram
  deriving DecidableEq

open Classical in
/-- **$\overline G$ for the stabilizer of a maximal hermitian lattice** (GHY 2001, Tables 1–2; split places: $K_v\cong GL_m(A_v)$,
§4 p. 109). `isNorm` is "$\alpha\in NE^\times$", $\alpha$ the discriminant of $V_v$ (for $E$ unramified and $\alpha$ a unit or
a uniformizer, $\alpha\in A^\times$ iff $\alpha\in NE^\times$, which is how Table 1 is read). Odd $m = 2n+1$: $U_{2n+1}$,
$U_{2n}\times U_1$, $\mathbb Z/2\times Sp_{2n}$; even $m = 2n$: $U_{2n}$, $U_{2n-1}\times U_1$, $Sp_{2n}$, $Sp_{2n-2}\times{}^2O_2$. -/
@[kb "ganhankeyu2001" "Tables 1–2, pp. 106–107 (column G-bar)"]
def unitaryGbar (m : ℕ) (e : LocalExt) (isNorm : Prop) : RedGrp :=
  match e with
  | .split => .GL m
  | .inert => if isNorm then .U m else .prod (.U (m - 1)) (.U 1)
  | .ram =>
    if Even m then (if isNorm then .Sp (m / 2) else .prod (.Sp (m / 2 - 1)) (.Ominus 1))
    else .prod .Z2 (.Sp (m / 2))

open Classical in
/-- **$\overline H{}^0$ for the unitary group** (GHY 2001, Tables 1–2): $GL_m$ (split), $U_m$ ($E$ unramified),
$SO_{2n+1}$ ($m = 2n+1$, $E$ ramified), $Sp_{2n}$ ($m = 2n$, $E$ ramified). -/
@[kb "ganhankeyu2001" "Tables 1–2, pp. 106–107 (column H-bar^0)"]
def unitaryHbar (m : ℕ) (e : LocalExt) : RedGrp :=
  match e with
  | .split => .GL m
  | .inert => .U m
  | .ram => if Even m then .Sp (m / 2) else .SOodd (m / 2)

/-- **The set $S$ of Proposition 4.4** ($m$ odd): $L_v$ ramified, or $L_v$ unramified and $\alpha\notin NL_v^\times$. -/
@[kb "ganhankeyu2001" "Proposition 4.4, p. 110 (the set S)"]
def InS44 (e : LocalExt) (isNorm : Prop) : Prop := e = .ram ∨ (e = .inert ∧ ¬ isNorm)

/-- **The set $S$ of Proposition 4.5** ($m$ even): $v$ does not split in $L$ and $\alpha\notin NL_v^\times$. -/
@[kb "ganhankeyu2001" "Proposition 4.5, p. 110 (the set S)"]
def InS45 (e : LocalExt) (isNorm : Prop) : Prop := e ≠ .split ∧ ¬ isNorm

open Classical in
/-- **$\lambda_v$ of Proposition 4.4 as printed** ($m = 2n+1$): $\frac12$ if $L_v$ is ramified, $(q_v^m+1)/(q_v+1)$ if $L_v$
is unramified and $\alpha\notin NL_v^\times$; $1$ for $v\notin S$. -/
@[kb "ganhankeyu2001" "Proposition 4.4, p. 110 (λ_v)"]
def lambdaProp44 (m : ℕ) (e : LocalExt) (isNorm : Prop) (q : ℝ) : ℝ :=
  if e = .ram then 1 / 2 else if InS44 e isNorm then (q ^ m + 1) / (q + 1) else 1

open Classical in
/-- **$\lambda_v$ of Proposition 4.5 as printed** ($m = 2n$): $(q_v^m-1)/(q_v+1)$ if $L_v$ is unramified,
$\frac12(q_v^m-1)/(q_v+1)$ if $L_v$ is ramified (for $v\in S$); $1$ for $v\notin S$. -/
@[kb "ganhankeyu2001" "Proposition 4.5, p. 110 (λ_v)"]
def lambdaProp45 (m : ℕ) (e : LocalExt) (isNorm : Prop) (q : ℝ) : ℝ :=
  if InS45 e isNorm then (if e = .inert then (q ^ m - 1) / (q + 1) else 1 / 2 * ((q ^ m - 1) / (q + 1))) else 1

open Classical in
/-- **GHY's (2.12) gives Proposition 4.4's $\lambda_v$** ($m = 2n+1$ odd): for the types of Table 1, the volume ratio is
$\frac12$ (ramified), $(q^m+1)/(q+1)$ (unramified, $\alpha\notin NE^\times$) and $1$ otherwise. -/
@[kb "ganhankeyu2001" "Table 1 and Proposition 4.4, pp. 106, 110"]
theorem lam_unitary_odd {q : ℝ} (hq : 1 < q) (n : ℕ) (e : LocalExt) (isNorm : Prop) :
    lam (unitaryHbar (2 * n + 1) e) (unitaryGbar (2 * n + 1) e isNorm) q =
      lambdaProp44 (2 * n + 1) e isNorm q := by
  have hodd : ¬ Even (2 * n + 1) := Nat.not_even_iff_odd.2 ⟨n, rfl⟩
  have h2 : (2 * n + 1) / 2 = n := by omega
  cases e with
  | split => simp [unitaryHbar, unitaryGbar, lambdaProp44, InS44, lam_self hq]
  | inert =>
    by_cases hN : isNorm
    · simp [unitaryHbar, unitaryGbar, lambdaProp44, InS44, hN, lam_self hq]
    · simp only [unitaryHbar, unitaryGbar, lambdaProp44, InS44, hN, ite_false]
      rw [show 2 * n + 1 - 1 = 2 * n by omega, table1_row2 hq n]
      simp
  | ram =>
    simp only [unitaryHbar, unitaryGbar, lambdaProp44, hodd, ite_false, h2, ite_true]
    exact table1_row3 hq n

open Classical in
/-- **GHY's (2.12) gives Proposition 4.5's $\lambda_v$** ($m = 2n$, $n\ge1$): for the types of Table 2. -/
@[kb "ganhankeyu2001" "Table 2 and Proposition 4.5, pp. 107, 110"]
theorem lam_unitary_even {q : ℝ} (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n) (e : LocalExt) (isNorm : Prop) :
    lam (unitaryHbar (2 * n) e) (unitaryGbar (2 * n) e isNorm) q = lambdaProp45 (2 * n) e isNorm q := by
  have hev : Even (2 * n) := ⟨n, by ring⟩
  have h2 : 2 * n / 2 = n := by omega
  cases e with
  | split => simp [unitaryHbar, unitaryGbar, lambdaProp45, InS45, lam_self hq]
  | inert =>
    by_cases hN : isNorm
    · simp [unitaryHbar, unitaryGbar, lambdaProp45, InS45, hN, lam_self hq]
    · simp only [unitaryHbar, unitaryGbar, lambdaProp45, InS45, hN, ite_false]
      rw [table2_row2 hq hn]
      simp
  | ram =>
    by_cases hN : isNorm
    · simp [unitaryHbar, unitaryGbar, lambdaProp45, InS45, hN, hev, lam_self hq]
    · simp only [unitaryHbar, unitaryGbar, lambdaProp45, InS45, hN, hev, ite_true, ite_false, h2]
      rw [table2_row4 hq hn]
      simp

open Classical in
/-- **$\overline G$ for the stabilizer of a maximal quaternionic hermitian lattice** (GHY 2001, (8.5); at $v\notin S_D$ the
stabilizer is hyperspecial, $\overline G = Sp_{2m}$, §9 p. 121): $\mathrm{Res}\,Sp_{2n}$ ($m = 2n$),
$\mathrm{Res}\,Sp_{2n}\times U_1$ ($m = 2n+1$) at $v\in S_D$. -/
@[kb "ganhankeyu2001" "(8.5), p. 120; §9, p. 121"]
def quatGbar (m : ℕ) (ram : Prop) : RedGrp :=
  if ram then (if Even m then .resSp (m / 2) else .prod (.resSp (m / 2)) (.U 1)) else .Sp m

open Classical in
/-- **$\overline G$ for the stabilizer of a maximal integral quaternionic hermitian lattice** (GHY 2001, (8.9); hyperspecial
$Sp_{2m}$ at $v\notin S_D$, §9 p. 122): $U_m$ at $v\in S_D$. -/
@[kb "ganhankeyu2001" "(8.9), p. 121; §9, p. 122"]
def quatIntGbar (m : ℕ) (ram : Prop) : RedGrp := if ram then .U m else .Sp m

/-- **$\lambda_v$ of Proposition 9.3 as printed** ($v\in S_D$): $\prod_{r=1}^n(q^{4r-2}-1)$ ($m = 2n$),
$\prod_{r=1}^n(q^{4r-2}-1)\cdot(q^{4n+2}-1)/(q+1)$ ($m = 2n+1$). -/
@[kb "ganhankeyu2001" "Proposition 9.3, p. 122 (λ_v); (8.6), p. 121"]
def lambdaProp93 (m : ℕ) (q : ℝ) : ℝ :=
  if Even m then ∏ r ∈ range (m / 2), (q ^ (4 * (r + 1) - 2) - 1)
  else (∏ r ∈ range (m / 2), (q ^ (4 * (r + 1) - 2) - 1)) * ((q ^ (4 * (m / 2) + 2) - 1) / (q + 1))

/-- **$\lambda_v$ of Proposition 9.4 as printed** ($v\in S_D$): $\prod_{r=1}^m(q^r+(-1)^r)$. -/
@[kb "ganhankeyu2001" "Proposition 9.4, p. 122 (λ_v); (8.10), p. 121"]
def lambdaProp94 (m : ℕ) (q : ℝ) : ℝ := ∏ r ∈ range m, (q ^ (r + 1) + (-1) ^ (r + 1))

open Classical in
/-- **GHY's (2.12) gives Proposition 9.3's $\lambda_v$**, and $\lambda_v = 1$ at $v\notin S_D$. -/
@[kb "ganhankeyu2001" "(8.6) and Proposition 9.3, pp. 121–122"]
theorem lam_quat {q : ℝ} (hq : 1 < q) (m : ℕ) (ram : Prop) :
    lam (.Sp m) (quatGbar m ram) q = if ram then lambdaProp93 m q else 1 := by
  by_cases hr : ram
  · simp only [quatGbar, hr, ite_true, lambdaProp93]
    by_cases hev : Even m
    · obtain ⟨n, rfl⟩ := hev
      rw [show n + n = 2 * n by ring]
      simp only [show Even (2 * n) from ⟨n, by ring⟩, ite_true, show 2 * n / 2 = n by omega]
      exact eq8_6_even hq n
    · obtain ⟨n, rfl⟩ := Nat.not_even_iff_odd.1 hev
      simp only [hev, ite_false, show (2 * n + 1) / 2 = n by omega]
      exact eq8_6_odd hq n
  · simp [quatGbar, hr, lam_self hq]

open Classical in
/-- **GHY's (2.12) gives Proposition 9.4's $\lambda_v$**, and $\lambda_v = 1$ at $v\notin S_D$. -/
@[kb "ganhankeyu2001" "(8.10) and Proposition 9.4, pp. 121–122"]
theorem lam_quatInt {q : ℝ} (hq : 1 < q) (m : ℕ) (ram : Prop) :
    lam (.Sp m) (quatIntGbar m ram) q = if ram then lambdaProp94 m q else 1 := by
  by_cases hr : ram
  · simp only [quatIntGbar, hr, ite_true, lambdaProp94]
    exact eq8_10 hq m
  · simp [quatIntGbar, hr, lam_self hq]

end QuadFormsKB.GanHankeYu2001
