/-
# Kitaoka 1993, §5.6: the exact kernel count modulo $p^t$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, used for Theorem 5.6.4 (e), p. 116
(there the number of homomorphisms $M \to (p^tN' \cap N)/p^tN$ is an index, with equality once $p^t N' \subseteq N$).

**Statement.** Let $p$ be a prime, $C \in M_n(\mathbb Z_p)$ with $\det C \neq 0$, and $t \ge 0$ with
$\det C \mid p^t$.  Residues modulo $p^t$ are the numbers $0 \le a < p^t$ (`Fin (p ^ t)`), cast to $\mathbb Z_p$.
Then
$$\#\{y \in \{0,\dots,p^t-1\}^n : Cy \equiv 0 \bmod p^t\} = \lVert\det C\rVert_p^{-1},$$
and for $n \times m$ matrices $Y$ with $CY \equiv 0 \bmod p^t$ the count is $\lVert\det C\rVert_p^{-m}$.

**Proves**
* `card_ker_eq` : the exact one-column count;
* `card_ker_mat_eq` : the exact count for $n \times m$ matrices (columns independent).

*Proof sketch.* The map $y \mapsto [z(y)]$, where $Cy = p^t z(y)$, into $\mathbb Z_p^n / C\mathbb Z_p^n$ is injective
(`Ch5KernelCount`).  It is also surjective when $\det C \mid p^t$: write $p^t = \det C \cdot u$.  For
$z \in \mathbb Z_p^n$ put $y_0 = \operatorname{adj}(C)(u z)$, so $C y_0 = \det C \cdot u\, z = p^t z$.  Reduce $y_0$
entrywise to residues $y = y_0 + p^t w'$.  Then $Cy = p^t (z + Cw')$, so $z(y) = z + Cw'$ (cancel $p^t$ in the
domain $\mathbb Z_p$), which has the class of $z$.  Hence the count equals
$\#(\mathbb Z_p^n / C\mathbb Z_p^n) = \lVert\det C\rVert_p^{-1}$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5KernelCount
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Stabilization

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- **Exact kernel count** (Kitaoka, Thm 5.6.4 (e), p. 116).  If $\det C \ne 0$ and $\det C \mid p^t$, the number of
residue vectors $y \in \{0,\dots,p^t-1\}^n$ with $Cy \equiv 0 \bmod p^t$ is exactly
$\lVert\det C\rVert_p^{-1} = [\mathbb Z_p^n : C\mathbb Z_p^n]$. -/
theorem card_ker_eq' (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) (t : ℕ)
    (ht : ∃ C' : Matrix (Fin n) (Fin n) ℤ_[p], C * C' = (p : ℤ_[p]) ^ t • 1) :
    (Nat.card {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i} : ℝ) = ‖C.det‖⁻¹ := by
  obtain ⟨hfin, hcard⟩ := card_quot_range C hC
  have hinj := mulVecLin_injective_of_det_ne_zero C hC
  set N : Submodule ℤ_[p] (Fin n → ℤ_[p]) := LinearMap.range C.mulVecLin with hN
  have hpt : (p : ℤ_[p]) ^ t ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hex : ∀ y : {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i},
      ∃ z : Fin n → ℤ_[p], (C *ᵥ fun j => (((y.1 j : ℕ)) : ℤ_[p])) = (p : ℤ_[p]) ^ t • z := by
    intro y
    choose z hz using y.2
    exact ⟨z, funext fun i => by simpa using hz i⟩
  choose z hz using hex
  let F : {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i} →
      ((Fin n → ℤ_[p]) ⧸ N) := fun y => Submodule.Quotient.mk (z y)
  have hF : Function.Injective F := by
    intro y y' hyy
    have hmem : z y - z y' ∈ N := (Submodule.Quotient.eq N).1 hyy
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hmem
    have key : C *ᵥ ((fun j => (((y.1 j : ℕ)) : ℤ_[p])) - fun j => (((y'.1 j : ℕ)) : ℤ_[p]))
        = C *ᵥ ((p : ℤ_[p]) ^ t • w) := by
      rw [Matrix.mulVec_sub, hz y, hz y', Matrix.mulVec_smul, ← smul_sub]
      congr 1
      exact hw.symm
    have key2 := hinj key
    apply Subtype.ext
    funext j
    apply fin_eq_of_dvd
    have := congrFun key2 j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    exact ⟨w j, this⟩
  have hS : Function.Surjective F := by
    intro q
    obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨C', hC'⟩ := ht
    set y0 : Fin n → ℤ_[p] := C' *ᵥ z0 with hy0
    have hCy0 : C *ᵥ y0 = (p : ℤ_[p]) ^ t • z0 := by
      rw [hy0, Matrix.mulVec_mulVec, hC', Matrix.smul_mulVec, Matrix.one_mulVec]
    choose w' hw' using fun j => red_spec (p := p) t (y0 j)
    let y : Fin n → Fin (p ^ t) := fun j => red p t (y0 j)
    have hycast : (fun j => (((y j : ℕ)) : ℤ_[p])) = y0 + (p : ℤ_[p]) ^ t • w' := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact hw' j
    have hCy : C *ᵥ (fun j => (((y j : ℕ)) : ℤ_[p])) = (p : ℤ_[p]) ^ t • (z0 + C *ᵥ w') := by
      rw [hycast, Matrix.mulVec_add, hCy0, Matrix.mulVec_smul, smul_add]
    have hmem : ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i := by
      intro i
      refine ⟨(z0 + C *ᵥ w') i, ?_⟩
      rw [hCy]; rfl
    refine ⟨⟨y, hmem⟩, ?_⟩
    have h1 : (p : ℤ_[p]) ^ t • z ⟨y, hmem⟩ = (p : ℤ_[p]) ^ t • (z0 + C *ᵥ w') := by
      rw [← hz ⟨y, hmem⟩]; exact hCy
    have h2 : z ⟨y, hmem⟩ = z0 + C *ᵥ w' := smul_right_injective _ hpt h1
    show Submodule.Quotient.mk (z ⟨y, hmem⟩) = Submodule.Quotient.mk z0
    rw [Submodule.Quotient.eq, h2]
    refine LinearMap.mem_range.2 ⟨w', ?_⟩
    simp
  have hbij : Function.Bijective F := ⟨hF, hS⟩
  rw [← hcard, Nat.card_congr (Equiv.ofBijective F hbij)]

/-- `card_ker_eq'` when $\det C \mid p^t$: then $C \cdot (u\operatorname{adj}C) = p^t1$ for $p^t = u\det C$. -/
theorem card_ker_eq (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) (t : ℕ)
    (ht : C.det ∣ (p : ℤ_[p]) ^ t) :
    (Nat.card {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i} : ℝ) = ‖C.det‖⁻¹ := by
  obtain ⟨u, hu⟩ := ht
  refine card_ker_eq' C hC t ⟨u • C.adjugate, ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hu, mul_comm]

/-- **Exact kernel count, $m$ columns** (Kitaoka, Thm 5.6.4 (e), p. 116).  If $\det C \ne 0$ and
$\det C \mid p^t$, the number of residue matrices $Y \in M_{n \times m}(\{0,\dots,p^t-1\})$ with
$CY \equiv 0 \bmod p^t$ is exactly $\lVert\det C\rVert_p^{-m}$. -/
theorem card_ker_mat_eq' (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) (t m : ℕ)
    (ht : ∃ C' : Matrix (Fin n) (Fin n) ℤ_[p], C * C' = (p : ℤ_[p]) ^ t • 1) :
    (Nat.card {Y : Matrix (Fin n) (Fin m) (Fin (p ^ t)) //
        ∀ i j, (p : ℤ_[p]) ^ t ∣ (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j} : ℝ) =
      ‖C.det‖⁻¹ ^ m := by
  let S := {y : Fin n → Fin (p ^ t) //
        ∀ i, (p : ℤ_[p]) ^ t ∣ (C *ᵥ fun j => (((y j : ℕ)) : ℤ_[p])) i}
  have hmul : ∀ (Y : Matrix (Fin n) (Fin m) (Fin (p ^ t))) i j,
      (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j =
        (C *ᵥ fun k => (((Y k j : Fin (p ^ t)) : ℕ) : ℤ_[p])) i := by
    intro Y i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  let e : {Y : Matrix (Fin n) (Fin m) (Fin (p ^ t)) //
        ∀ i j, (p : ℤ_[p]) ^ t ∣ (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j} ≃
      (Fin m → S) :=
    { toFun := fun Y j => ⟨fun k => Y.1 k j, fun i => by
        rw [← hmul]; exact Y.2 i j⟩
      invFun := fun f => ⟨Matrix.of fun k j => (f j).1 k, fun i j => by
        rw [hmul]; exact (f j).2 i⟩
      left_inv := fun Y => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [card_ker_eq' C hC t ht]

theorem card_ker_mat_eq (C : Matrix (Fin n) (Fin n) ℤ_[p]) (hC : C.det ≠ 0) (t m : ℕ)
    (ht : C.det ∣ (p : ℤ_[p]) ^ t) :
    (Nat.card {Y : Matrix (Fin n) (Fin m) (Fin (p ^ t)) //
        ∀ i j, (p : ℤ_[p]) ^ t ∣ (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j} : ℝ) =
      ‖C.det‖⁻¹ ^ m := by
  obtain ⟨u, hu⟩ := ht
  refine card_ker_mat_eq' C hC t m ⟨u • C.adjugate, ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hu, mul_comm]

end QuadFormsKB.Kitaoka.Density

end
