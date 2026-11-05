/-
# Lifting even forms modulo powers of 2, and the block count identity at $p = 2$ for type II

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, and (18), p. 281 (bibliography key `conwaysloane1988`).

At $p = 2$ the block count identity `card_fromBlocks_eq_sum` holds, but the perturbed blocks $U + 2W^{\mathsf T}BW$ and
$B + 2BWU^{-1}W^{\mathsf T}B$ need not be congruent to $U$ and $B$. They are when $U$ and $B$ have **even diagonal**
(the first two Jordan constituents of $U \oplus 2B$ have type II): then both perturbations have the shape
$S + SMS$ with $M = 2K$ and $K$ of even diagonal, and such a perturbation is a congruence modulo every power of $2$
(`exists_congr_even`, a Hensel-type successive approximation). Consequently (`card_fromBlocks_even`)
$$\#\{X : X^{\mathsf T}AX \equiv A \bmod 2^r\} = 2^{r\,ab}\cdot\#\{Y : Y^{\mathsf T}UY \equiv U\}\cdot
  \#\{Z : Z^{\mathsf T}(2B)Z \equiv 2B\}$$
for $A = U \oplus 2B$, and $\alpha_2(U \oplus 2B) = \alpha_2(U)\,\alpha_2(2B)$ (`alphaP_fromBlocks_even`).

**The approximation.** For $S$ symmetric with even diagonal, write $\mathrm{h}(X)$ (`halfUp`) for the upper triangle of
a symmetric $X$ with even diagonal, with the diagonal halved, so that $\mathrm h(X) + \mathrm h(X)^{\mathsf T} = X$. The
iteration $N_0 = 0$, $N_{k+1} = \mathrm h(M - N_k^{\mathsf T}SN_k)$ has $N_{k+1} - N_k \equiv 0 \pmod{2^{k+1}}$, and
$G = 1 + N_kS$ satisfies $G^{\mathsf T}SG \equiv S + SMS \pmod{2^{k+1}}$. Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.BlockCount
import QuadFormsKB.Literature.ConwaySloane.Mass.Density

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix Finset

section Integer

variable {n : ℕ}

/-- The upper triangle of $X$ with the diagonal halved: $\mathrm h(X)_{ij} = X_{ij}$ ($i < j$), $X_{ii}/2$, $0$
($i > j$). -/
def halfUp (X : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i < j then X i j else if i = j then X i i / 2 else 0

/-- Every diagonal entry is even. -/
def EvenDiag (X : Matrix (Fin n) (Fin n) ℤ) : Prop := ∀ i, 2 ∣ X i i

/-- All entries divisible by $c$. -/
def AllDvd {m k : Type*} (c : ℤ) (X : Matrix m k ℤ) : Prop := ∀ i j, c ∣ X i j

theorem halfUp_add_transpose {X : Matrix (Fin n) (Fin n) ℤ} (hX : Xᵀ = X) (he : EvenDiag X) :
    halfUp X + (halfUp X)ᵀ = X := by
  ext i j
  simp only [Matrix.add_apply, transpose_apply, halfUp]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne']
  · obtain ⟨c, hc⟩ := he i
    simp only [lt_irrefl, if_false, if_true, hc]
    omega
  · have : X j i = X i j := by rw [← transpose_apply X i j, hX]
    simp [h, not_lt.mpr h.le, h.ne', this]

theorem halfUp_sub {X Y : Matrix (Fin n) (Fin n) ℤ} (hX : EvenDiag X) (hY : EvenDiag Y) :
    halfUp (X - Y) = halfUp X - halfUp Y := by
  ext i j
  simp only [halfUp, Matrix.sub_apply]
  split_ifs with h1 h2
  · rfl
  · subst h2
    obtain ⟨c, hc⟩ := hX i
    obtain ⟨d, hd⟩ := hY i
    rw [hc, hd]; omega
  · simp

theorem halfUp_dvd {X : Matrix (Fin n) (Fin n) ℤ} {m : ℕ} (h : AllDvd (2 ^ m) X)
    (hd : ∀ i, (2 : ℤ) ^ (m + 1) ∣ X i i) : AllDvd (2 ^ m) (halfUp X) := by
  intro i j
  simp only [halfUp]
  split_ifs with h1 h2
  · exact h i j
  · subst h2
    obtain ⟨c, hc⟩ := hd i
    rw [hc, show (2 : ℤ) ^ (m + 1) * c = 2 * (2 ^ m * c) by ring, Int.mul_ediv_cancel_left _ two_ne_zero]
    exact dvd_mul_right _ _
  · exact dvd_zero _

theorem allDvd_mul {m k l : Type*} [Fintype k] {c d : ℤ} {Y : Matrix m k ℤ} {Z : Matrix k l ℤ}
    (hY : AllDvd c Y) (hZ : AllDvd d Z) : AllDvd (c * d) (Y * Z) := fun i j =>
  Finset.dvd_sum fun x _ => mul_dvd_mul (hY i x) (hZ x j)

theorem allDvd_mul_left {m k l : Type*} [Fintype k] {c : ℤ} {Y : Matrix m k ℤ} (hY : AllDvd c Y)
    (Z : Matrix k l ℤ) : AllDvd c (Y * Z) := by
  have := allDvd_mul (d := 1) hY (fun _ _ => one_dvd _) (Z := Z); simpa using this

theorem allDvd_mul_right {m k l : Type*} [Fintype k] {c : ℤ} (Y : Matrix m k ℤ) {Z : Matrix k l ℤ}
    (hZ : AllDvd c Z) : AllDvd c (Y * Z) := by
  have := allDvd_mul (c := 1) (fun _ _ => one_dvd _) hZ (Y := Y); simpa using this

theorem allDvd_transpose {m k : Type*} {c : ℤ} {Y : Matrix m k ℤ} (hY : AllDvd c Y) : AllDvd c Yᵀ :=
  fun i j => hY j i

theorem allDvd_add {m k : Type*} {c : ℤ} {Y Z : Matrix m k ℤ} (hY : AllDvd c Y) (hZ : AllDvd c Z) :
    AllDvd c (Y + Z) := fun i j => dvd_add (hY i j) (hZ i j)

theorem allDvd_sub {m k : Type*} {c : ℤ} {Y Z : Matrix m k ℤ} (hY : AllDvd c Y) (hZ : AllDvd c Z) :
    AllDvd c (Y - Z) := fun i j => dvd_sub (hY i j) (hZ i j)

theorem allDvd_of_dvd {m k : Type*} {c d : ℤ} (hcd : c ∣ d) {Y : Matrix m k ℤ} (hY : AllDvd d Y) :
    AllDvd c Y := fun i j => hcd.trans (hY i j)

/-- For $S$ symmetric with even diagonal, $(Y^{\mathsf T}SY)_{ii} = 2(Y^{\mathsf T}\mathrm h(S)Y)_{ii}$. -/
theorem diag_quad {k : Type*} [Fintype k] {S : Matrix (Fin n) (Fin n) ℤ} (hS : Sᵀ = S) (he : EvenDiag S)
    (Y : Matrix (Fin n) k ℤ) (i : k) : (Yᵀ * S * Y) i i = 2 * (Yᵀ * halfUp S * Y) i i := by
  have h : Yᵀ * S * Y = Yᵀ * halfUp S * Y + (Yᵀ * halfUp S * Y)ᵀ := by
    conv_lhs => rw [← halfUp_add_transpose hS he]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [h, Matrix.add_apply, transpose_apply]; ring

theorem quad_symm {k : Type*} [Fintype k] {S : Matrix (Fin n) (Fin n) ℤ} (hS : Sᵀ = S)
    (Y : Matrix (Fin n) k ℤ) : (Yᵀ * S * Y)ᵀ = Yᵀ * S * Y := by
  simp [Matrix.mul_assoc, hS]

theorem quad_evenDiag {S : Matrix (Fin n) (Fin n) ℤ} (hS : Sᵀ = S) (he : EvenDiag S)
    (Y : Matrix (Fin n) (Fin n) ℤ) : EvenDiag (Yᵀ * S * Y) := fun i =>
  ⟨_, diag_quad hS he Y i⟩

variable (S M : Matrix (Fin n) (Fin n) ℤ)

/-- The approximation $N_0 = 0$, $N_{k+1} = \mathrm h(M - N_k^{\mathsf T}SN_k)$. -/
def iter : ℕ → Matrix (Fin n) (Fin n) ℤ
  | 0 => 0
  | k + 1 => halfUp (M - (iter k)ᵀ * S * iter k)

variable {S M}

section Hyp

variable (hS : Sᵀ = S) (hSe : EvenDiag S) (hM : Mᵀ = M) (hM2 : AllDvd 2 M) (hM4 : ∀ i, (4 : ℤ) ∣ M i i)
include hS hSe hM hM2 hM4

theorem evenDiag_sub (N : Matrix (Fin n) (Fin n) ℤ) : EvenDiag (M - Nᵀ * S * N) := fun i => by
  rw [Matrix.sub_apply]
  exact dvd_sub ((by norm_num : (2 : ℤ) ∣ 4).trans (hM4 i)) (quad_evenDiag hS hSe N i)

theorem iter_even : ∀ k, AllDvd 2 (iter S M k)
  | 0 => fun _ _ => dvd_zero _
  | k + 1 => by
    have ih := iter_even k
    refine halfUp_dvd (m := 1) ?_ ?_
    · have h4 : AllDvd (2 * 2) ((iter S M k)ᵀ * S * iter S M k) :=
        allDvd_mul (allDvd_mul_left (allDvd_transpose ih) S) ih
      simpa using allDvd_sub hM2 (allDvd_of_dvd (by norm_num) h4)
    · intro i
      rw [Matrix.sub_apply]
      refine dvd_sub (by simpa using hM4 i) ?_
      rw [diag_quad hS hSe]
      have h4 : AllDvd (2 * 2) ((iter S M k)ᵀ * halfUp S * iter S M k) :=
        allDvd_mul (allDvd_mul_left (allDvd_transpose ih) _) ih
      have := h4 i i
      obtain ⟨c, hc⟩ := this
      rw [hc]; exact ⟨2 * c, by ring⟩

/-- The error term: with $D = N' - N$, $N'^{\mathsf T}SN' - N^{\mathsf T}SN = D^{\mathsf T}SN + N^{\mathsf T}SD +
D^{\mathsf T}SD$ is divisible by $2^{m+2}$ when $D$ is divisible by $2^{m+1}$ and $N$ by $2$; its diagonal by
$2^{m+3}$. -/
theorem err_dvd {N N' : Matrix (Fin n) (Fin n) ℤ} {m : ℕ} (hN : AllDvd 2 N) (hD : AllDvd (2 ^ (m + 1)) (N' - N)) :
    AllDvd (2 ^ (m + 2)) (N'ᵀ * S * N' - Nᵀ * S * N) ∧
      ∀ i, (2 : ℤ) ^ (m + 3) ∣ (N'ᵀ * S * N' - Nᵀ * S * N) i i := by
  set D := N' - N with hDdef
  have hN' : N' = N + D := by rw [hDdef]; abel
  have e : N'ᵀ * S * N' - Nᵀ * S * N = Dᵀ * S * N + (Dᵀ * S * N)ᵀ + Dᵀ * S * D := by
    rw [hN']
    simp only [transpose_add, transpose_mul, hS, transpose_transpose, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  have h1 : AllDvd (2 ^ (m + 1) * 2) (Dᵀ * S * N) := allDvd_mul (allDvd_mul_left (allDvd_transpose hD) S) hN
  have h2 : AllDvd (2 ^ (m + 1) * 2 ^ (m + 1)) (Dᵀ * S * D) :=
    allDvd_mul (allDvd_mul_left (allDvd_transpose hD) S) hD
  have h2' : AllDvd (2 ^ (m + 1) * 2 ^ (m + 1)) (Dᵀ * halfUp S * D) :=
    allDvd_mul (allDvd_mul_left (allDvd_transpose hD) _) hD
  have p1 : (2 : ℤ) ^ (m + 2) ∣ 2 ^ (m + 1) * 2 := ⟨1, by ring⟩
  have p2 : (2 : ℤ) ^ (m + 2) ∣ 2 ^ (m + 1) * 2 ^ (m + 1) := ⟨2 ^ m, by ring⟩
  refine ⟨?_, fun i => ?_⟩
  · rw [e]
    exact allDvd_add (allDvd_add (allDvd_of_dvd p1 h1) (allDvd_transpose (allDvd_of_dvd p1 h1)))
      (allDvd_of_dvd p2 h2)
  · rw [e, Matrix.add_apply, Matrix.add_apply, transpose_apply, diag_quad hS hSe D i]
    obtain ⟨c, hc⟩ := h1 i i
    obtain ⟨d, hd⟩ := h2' i i
    rw [hc, hd]
    exact ⟨c + 2 ^ m * d, by ring⟩

theorem iter_succ_sub : ∀ k, AllDvd (2 ^ (k + 1)) (iter S M (k + 1) - iter S M k)
  | 0 => by
    simp only [iter, transpose_zero, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    refine halfUp_dvd (m := 1) (by simpa using hM2) fun i => by simpa using hM4 i
  | k + 1 => by
    have ih := iter_succ_sub k
    have hE := err_dvd hS hSe hM hM2 hM4 (iter_even hS hSe hM hM2 hM4 k) ih
    have e : iter S M (k + 1 + 1) - iter S M (k + 1) =
        halfUp ((iter S M k)ᵀ * S * iter S M k - (iter S M (k + 1))ᵀ * S * iter S M (k + 1)) := by
      change halfUp (M - _) - halfUp (M - _) = _
      rw [← halfUp_sub (evenDiag_sub hS hSe hM hM2 hM4 _) (evenDiag_sub hS hSe hM hM2 hM4 _)]
      congr 1; abel
    rw [e]
    refine halfUp_dvd ?_ fun i => ?_
    · have := hE.1
      intro i j
      have h := this i j
      rw [show (iter S M k)ᵀ * S * iter S M k - (iter S M (k + 1))ᵀ * S * iter S M (k + 1) =
        -((iter S M (k + 1))ᵀ * S * iter S M (k + 1) - (iter S M k)ᵀ * S * iter S M k) by abel, Matrix.neg_apply]
      exact (dvd_neg).mpr h
    · have h := hE.2 i
      rw [show (iter S M k)ᵀ * S * iter S M k - (iter S M (k + 1))ᵀ * S * iter S M (k + 1) =
        -((iter S M (k + 1))ᵀ * S * iter S M (k + 1) - (iter S M k)ᵀ * S * iter S M k) by abel, Matrix.neg_apply]
      exact (dvd_neg).mpr h

/-- **Hensel's lemma for even forms** (integer form): for $S$ symmetric with even diagonal and $M$ symmetric with
$M \equiv 0 \pmod 2$ and diagonal $\equiv 0 \pmod 4$, for every $r$ there is $N \equiv 0 \pmod 2$ with
$(1 + NS)^{\mathsf T}S(1 + NS) \equiv S + SMS \pmod{2^r}$. -/
theorem exists_approx (r : ℕ) : ∃ N : Matrix (Fin n) (Fin n) ℤ, AllDvd 2 N ∧
    AllDvd (2 ^ r) ((1 + N * S)ᵀ * S * (1 + N * S) - (S + S * M * S)) := by
  refine ⟨iter S M (r + 1), iter_even hS hSe hM hM2 hM4 _, ?_⟩
  set N := iter S M (r + 1)
  set N₀ := iter S M r
  have hfix : N + Nᵀ = M - N₀ᵀ * S * N₀ :=
    halfUp_add_transpose (by rw [transpose_sub, hM, quad_symm hS]) (evenDiag_sub hS hSe hM hM2 hM4 _)
  have hE := (err_dvd hS hSe hM hM2 hM4 (iter_even hS hSe hM hM2 hM4 r) (iter_succ_sub hS hSe hM hM2 hM4 r)).1
  have e : (1 + N * S)ᵀ * S * (1 + N * S) - (S + S * M * S) =
      S * (Nᵀ * S * N - N₀ᵀ * S * N₀) * S := by
    have : M = N + Nᵀ + N₀ᵀ * S * N₀ := by rw [hfix]; abel
    rw [this]
    simp only [transpose_add, transpose_one, transpose_mul, hS, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e]
  exact allDvd_mul_left (allDvd_mul_right S (allDvd_of_dvd (pow_dvd_pow 2 (by omega)) hE)) S

end Hyp

end Integer

section ZModVersion

variable {n : ℕ} {r : ℕ}

/-- The reduction $\mathbb Z \to \mathbb Z/2^r$ of an integer matrix. -/
abbrev red (r : ℕ) {m k : Type*} (X : Matrix m k ℤ) : Matrix m k (ZMod (2 ^ r)) :=
  X.map (Int.castRingHom (ZMod (2 ^ r)))

theorem red_eq_of_allDvd {m k : Type*} {X Y : Matrix m k ℤ} (h : AllDvd (2 ^ r) (X - Y)) : red r X = red r Y := by
  ext i j
  have := h i j
  simp only [map_apply, Int.coe_castRingHom]
  rw [← sub_eq_zero, ← Int.cast_sub]
  have h' : ((2 ^ r : ℕ) : ℤ) ∣ X i j - Y i j := by simpa using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h'

theorem red_mul {m k l : Type*} [Fintype k] (X : Matrix m k ℤ) (Y : Matrix k l ℤ) :
    red r (X * Y) = red r X * red r Y := Matrix.map_mul

theorem red_add {m k : Type*} (X Y : Matrix m k ℤ) : red r (X + Y) = red r X + red r Y := Matrix.map_add _ (map_add _) _ _

theorem red_sub {m k : Type*} (X Y : Matrix m k ℤ) : red r (X - Y) = red r X - red r Y := Matrix.map_sub _ (map_sub _) _ _

theorem red_transpose {m k : Type*} (X : Matrix m k ℤ) : red r Xᵀ = (red r X)ᵀ := (Matrix.transpose_map ..).symm

theorem red_one {m : Type*} [DecidableEq m] : red r (1 : Matrix m m ℤ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem red_smul {m k : Type*} (c : ℤ) (X : Matrix m k ℤ) : red r (c • X) = (c : ZMod (2 ^ r)) • red r X := by
  ext i j; simp [Matrix.smul_apply]

theorem two_nilpotent (r : ℕ) : IsNilpotent (2 : ZMod (2 ^ r)) :=
  ⟨r, by exact_mod_cast ZMod.natCast_self (2 ^ r)⟩

/-- **Hensel's lemma for even forms modulo $2^r$**: for integer $S$ symmetric with even diagonal and $M$ symmetric
with $M \equiv 0 \pmod 2$ and diagonal $\equiv 0 \pmod 4$, there is an invertible $G$ over $\mathbb Z/2^r$ with
$G^{\mathsf T}SG = S + SMS$. -/
@[kb "conwaysloane1988" "(18), p. 281 (lifting even forms modulo powers of 2)"]
theorem exists_congr_even {S M : Matrix (Fin n) (Fin n) ℤ} (hS : Sᵀ = S) (hSe : EvenDiag S) (hM : Mᵀ = M)
    (hM2 : AllDvd 2 M) (hM4 : ∀ i, (4 : ℤ) ∣ M i i) :
    ∃ G : Matrix (Fin n) (Fin n) (ZMod (2 ^ r)), IsUnit G ∧
      Gᵀ * red r S * G = red r S + red r S * red r M * red r S := by
  obtain ⟨N, hN, hE⟩ := exists_approx hS hSe hM hM2 hM4 r
  refine ⟨red r (1 + N * S), ?_, ?_⟩
  · have hN' : red r N = (2 : ZMod (2 ^ r)) • red r (fun i j => N i j / 2) := by
      ext i j
      obtain ⟨c, hc⟩ := hN i j
      change ((N i j : ℤ) : ZMod (2 ^ r)) = (2 : ZMod (2 ^ r)) * ((N i j / 2 : ℤ) : ZMod (2 ^ r))
      rw [hc, Int.mul_ediv_cancel_left _ two_ne_zero]; push_cast; ring
    have hnil : IsNilpotent (red r N * red r S) := by
      rw [hN', Matrix.smul_mul]
      exact isNilpotent_smul (two_nilpotent r) _
    have : red r (1 + N * S) = 1 + red r N * red r S := by
      rw [red_add, red_one, red_mul]
    rw [this, add_comm]
    exact hnil.isUnit_add_one
  · have := red_eq_of_allDvd hE
    simp only [red_mul, red_add, red_transpose, red_one] at this ⊢; exact this

end ZModVersion

section Blocks

variable {a b r : ℕ}

/-- The integer lift $x \mapsto \operatorname{val} x$ of a matrix over $\mathbb Z/2^r$. -/
def lift {m k : Type*} (X : Matrix m k (ZMod (2 ^ r))) : Matrix m k ℤ := X.map fun x => (x.val : ℤ)

theorem red_lift [NeZero (2 ^ r)] {m k : Type*} (X : Matrix m k (ZMod (2 ^ r))) : red r (lift X) = X := by
  ext i j; simp [lift]

/-- **The block count identity at $p = 2$ when the first two constituents have type II**: for $U$ ($a \times a$)
and $B$ ($b \times b$) integral symmetric with even diagonal and $\det U$ odd, over $\mathbb Z/2^r$,
$\#\{X : X^{\mathsf T}(U \oplus 2B)X = U \oplus 2B\} = |M_{b\times a}|\cdot\#\{Y : Y^{\mathsf T}UY = U\}\cdot
\#\{Z : Z^{\mathsf T}(2B)Z = 2B\}$. -/
@[kb "conwaysloane1988" "(18), p. 281 (splitting off a type II unimodular constituent, p = 2)"]
theorem card_fromBlocks_even [NeZero (2 ^ r)] {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}
    (hUs : Uᵀ = U) (hUe : EvenDiag U) (hU : IsUnit (red r U).det) (hBs : Bᵀ = B) (hBe : EvenDiag B) :
    Nat.card {X : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (ZMod (2 ^ r)) //
        Xᵀ * fromBlocks (red r U) 0 0 ((2 : ZMod (2 ^ r)) • red r B) * X =
          fromBlocks (red r U) 0 0 ((2 : ZMod (2 ^ r)) • red r B)} =
      Fintype.card (Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) *
        Nat.card {Y : Matrix (Fin a) (Fin a) (ZMod (2 ^ r)) // Yᵀ * red r U * Y = red r U} *
        Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
          Zᵀ * ((2 : ZMod (2 ^ r)) • red r B) * Z = (2 : ZMod (2 ^ r)) • red r B} := by
  set Ub := red r U
  set Bb := red r B
  have hUbs : Ubᵀ = Ub := by rw [← red_transpose, hUs]
  have hBbs : Bbᵀ = Bb := by rw [← red_transpose, hBs]
  have hCs : ((2 : ZMod (2 ^ r)) • Bb)ᵀ = (2 : ZMod (2 ^ r)) • Bb := by rw [transpose_smul, hBbs]
  set V := Ub⁻¹ with hV
  have hVs : Vᵀ = V := by rw [hV, transpose_nonsing_inv, hUbs]
  have hUV : Ub * V = 1 := Matrix.mul_nonsing_inv _ hU
  have hVU : V * Ub = 1 := Matrix.nonsing_inv_mul _ hU
  rw [card_fromBlocks_eq_sum hUbs hU hCs (two_nilpotent r) rfl, mul_assoc, ← Finset.card_univ, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hW : red r (lift W) = W := red_lift W
  have hVl : red r (lift V) = V := red_lift V
  congr 1
  · -- the first block
    set Y := lift W * lift V
    have hY : red r Y = W * V := by rw [red_mul, hW, hVl]
    obtain ⟨G, hG, hGe⟩ := exists_congr_even (r := r) (S := U) (M := (2 : ℤ) • (Yᵀ * B * Y)) hUs hUe
      (by rw [transpose_smul, quad_symm hBs])
      (fun i j => by simp [Matrix.smul_apply])
      (fun i => by
        rw [Matrix.smul_apply, smul_eq_mul, diag_quad hBs hBe]
        exact ⟨_, by ring⟩)
    have e : pertU Ub ((2 : ZMod (2 ^ r)) • Bb) W = Gᵀ * Ub * G := by
      rw [hGe, pertU]
      congr 1
      have h2 : red r ((2 : ℤ) • (Yᵀ * B * Y)) = (2 : ZMod (2 ^ r)) • ((W * V)ᵀ * Bb * (W * V)) := by
        rw [red_smul, red_mul, red_mul, red_transpose, hY]; norm_num; rfl
      rw [h2, transpose_mul, hVs]
      have hVU' : V * red r U = 1 := hVU
      have hUV' : red r U * V = 1 := hUV
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [hVU', Matrix.mul_one, ← Matrix.mul_assoc (red r U) V, hUV', Matrix.one_mul]
    rw [e, card_congr_unit hG]
  · -- the second block
    set Y := lift V * (lift W)ᵀ
    have hY : red r Y = V * Wᵀ := by rw [red_mul, red_transpose, hW, hVl]
    obtain ⟨G, hG, hGe⟩ := exists_congr_even (r := r) (S := B) (M := (2 : ℤ) • (Yᵀ * U * Y)) hBs hBe
      (by rw [transpose_smul, quad_symm hUs])
      (fun i j => by simp [Matrix.smul_apply])
      (fun i => by
        rw [Matrix.smul_apply, smul_eq_mul, diag_quad hUs hUe]
        exact ⟨_, by ring⟩)
    have e : pertC Ub ((2 : ZMod (2 ^ r)) • Bb) W = Gᵀ * ((2 : ZMod (2 ^ r)) • Bb) * G := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hGe, pertC]
      have h2 : red r ((2 : ℤ) • (Yᵀ * U * Y)) = (2 : ZMod (2 ^ r)) • (W * V * Wᵀ) := by
        rw [red_smul, red_mul, red_mul, red_transpose, hY, transpose_mul, transpose_transpose, hVs]
        have hUV' : red r U * V = 1 := hUV
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (red r U) V, hUV', Matrix.one_mul]; norm_num
      rw [h2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_add, smul_smul]
      norm_num
      rfl
    rw [e, card_congr_unit hG]

end Blocks

end QuadFormsKB.ConwaySloane.Mass.Two
