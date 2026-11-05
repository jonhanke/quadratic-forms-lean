/-
# Cassels, Chapter 8, §3: the canonical forms of Theorem 3.1 ($p \ne 2$)

**Canonical forms** ((3.9)–(3.14), pp. 115–116). Fix a quadratic non-residue $r$ of $p$ ($\lvert r\rvert_p = 1$,
$r \notin (\mathbb Q_p^{\times})^{2}$). For $\varepsilon \in \{0, 1\}$ and $m \ge 1$,
$h(\varepsilon, m, \vec y) = y_1^{2} + \cdots + y_{m-1}^{2} + r^{\varepsilon}y_m^{2}$, and a canonical form is
$\sum_{j=1}^{J} p^{e(j)}h(\varepsilon_j, m_j, \vec y^{(j)})$ in distinct variables, with
$e(1) < e(2) < \cdots < e(J)$ ($e(j) \in \mathbb Z$) and $\sum_j m_j = n$. Here a canonical form is described by the
list of its blocks $(e(j), \varepsilon_j, m_j)$ (`CanonBlock`, `IsCanon`), and its matrix is the diagonal matrix of the
list `canonEntries p r D` of its diagonal coefficients (block $j$ contributes $m_j - 1$ entries $p^{e(j)}$ followed by
$p^{e(j)}r^{\varepsilon_j}$), in the variables $x_0, \dots, x_{n-1}$ in this order.

Theorem 3.1 itself is `exists_unique_canonical` (`Ch8/Thm31.lean`); existence and uniqueness are proved in
`Ch8/CanonicalExists.lean` and `Ch8/CanonicalUnique.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Bases

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- A block $p^{e}h(\varepsilon, m, \vec y)$ of Cassels' canonical form (3.11): the exponent $e = e(j) \in \mathbb Z$, the
exponent $\varepsilon = \varepsilon_j \in \{0, 1\}$ of the non-residue and the dimension $m = m_j$. -/
@[kb "cassels1978" "Ch. 8, Thm. 3.1, (3.10)–(3.11), p. 116 (blocks of the canonical form)"]
structure CanonBlock where
  /-- The exponent $e(j)$ of $p$. -/
  e : ℤ
  /-- The exponent $\varepsilon_j \in \{0, 1\}$ of the non-residue $r$. -/
  ε : Fin 2
  /-- The number $m_j$ of variables of the block. -/
  m : ℕ
deriving DecidableEq

/-- Cassels' conditions (3.12)–(3.13) on the blocks: $e(1) < e(2) < \cdots$ and every $m_j \ge 1$. -/
@[kb "cassels1978" "Ch. 8, Thm. 3.1, (3.12)–(3.13), p. 116"]
def IsCanon (D : List CanonBlock) : Prop := D.IsChain (fun a b => a.e < b.e) ∧ ∀ b ∈ D, 1 ≤ b.m

variable (p) in
/-- The diagonal coefficients of the canonical form $\sum_j p^{e(j)}h(\varepsilon_j, m_j, \vec y^{(j)})$ with blocks
`D`: block $j$ gives $m_j - 1$ coefficients $p^{e(j)}$ and then $p^{e(j)}r^{\varepsilon_j}$ ((3.10)). -/
@[kb "cassels1978" "Ch. 8, Thm. 3.1, (3.10)–(3.11), p. 116 (the canonical form)"]
noncomputable def canonEntries (r : ℚ_[p]) (D : List CanonBlock) : List ℚ_[p] :=
  D.flatMap fun b => List.replicate (b.m - 1) ((p : ℚ_[p]) ^ b.e) ++ [(p : ℚ_[p]) ^ b.e * r ^ (b.ε : ℕ)]

/-- The canonical matrix: the diagonal matrix of `canonEntries p r D`, as an $n \times n$ matrix when the list has $n$
entries. -/
noncomputable def canonMat (r : ℚ_[p]) (D : List CanonBlock) (h : (canonEntries p r D).length = n) :
    Matrix (Fin n) (Fin n) ℚ_[p] :=
  Matrix.diagonal fun i => (canonEntries p r D)[(i : ℕ)]'(h ▸ i.2)

/-- $\mathbb Z_p$-equivalence of forms given by matrices over $\mathbb Q_p$: $G = T^{t}FT$ for some
$T \in \mathrm{GL}_n(\mathbb Z_p)$ (Cassels' "$f$ is $\mathbb Z_p$-equivalent to $g$", $g(\vec x) = f(T\vec x)$). -/
def ZpEquiv (F G : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop :=
  ∃ T : GL (Fin n) ℤ_[p], (T.val.map PadicInt.Coe.ringHom)ᵀ * F * T.val.map PadicInt.Coe.ringHom = G

theorem ZpEquiv.refl (F : Matrix (Fin n) (Fin n) ℚ_[p]) : ZpEquiv F F :=
  ⟨1, by simp [Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem ZpEquiv.symm {F G : Matrix (Fin n) (Fin n) ℚ_[p]} (h : ZpEquiv F G) : ZpEquiv G F := by
  obtain ⟨T, rfl⟩ := h
  refine ⟨T⁻¹, ?_⟩
  have hM : T.val.map PadicInt.Coe.ringHom * (T⁻¹).val.map PadicInt.Coe.ringHom = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  calc _ = (T.val.map PadicInt.Coe.ringHom * (T⁻¹).val.map PadicInt.Coe.ringHom)ᵀ * F *
        (T.val.map PadicInt.Coe.ringHom * (T⁻¹).val.map PadicInt.Coe.ringHom) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = F := by rw [hM]; simp

theorem ZpEquiv.trans {F G H : Matrix (Fin n) (Fin n) ℚ_[p]} (h₁ : ZpEquiv F G) (h₂ : ZpEquiv G H) :
    ZpEquiv F H := by
  obtain ⟨T, rfl⟩ := h₁
  obtain ⟨S, rfl⟩ := h₂
  refine ⟨T * S, ?_⟩
  rw [Units.val_mul, Matrix.map_mul]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

end QuadFormsKB.Cassels
