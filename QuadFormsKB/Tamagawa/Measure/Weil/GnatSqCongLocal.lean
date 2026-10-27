/-
# The local preimage of $K_m$ under $(\alpha,\beta)\mapsto(x\mapsto\alpha x\beta^{-1})$

**Layer:** a number field $F$, a finite place $v$ (dyadic places included), $a, b\in\mathcal O_F\setminus0$ with
$|2|_v = q^{-s}$, $|a|_v = q^{-e_a}$, $\Lambda_v = \mathfrak o_v\langle1,i,j,k\rangle$, $Q_0 = \langle1,-a,-b,ab\rangle$ (`qSq a b`).

For $(\alpha,\beta)$ with $\operatorname{nrd}\alpha = \operatorname{nrd}\beta$ and $\phi(\alpha,\beta) = (x\mapsto\alpha x\beta^{-1})\in SO(V)(F_v)$
(`sqSOK`), with $2s < m$, $s + e_a\le m$:
* **`sqSOK_mem_congSub`**: if $\beta\in\Lambda^{(m)}_v$ (`lamCong`) and $\alpha\beta^{-1}\in1+\pi^m\Lambda_v$ (`oneAddCong`),
  then $\phi(\alpha,\beta)\in K_m$;
* **`exists_smul_of_sqSOK_mem_congSub`**: conversely, if $\phi(\alpha,\beta)\in K_m$ then $(c\alpha, c\beta)$ satisfies these two
  conditions for some $c\in F_v^\times$ (namely $c = (\operatorname{re}\beta)^{-1}$).

*Proof.* The columns of $\phi(\alpha,\beta)$ are the coordinates of $\alpha e_j\beta^{-1}$ ($e_j = 1, i, j, k$). With
$\gamma = \alpha\beta^{-1} = \phi(\alpha,\beta)(1)$: $\alpha e_j\beta^{-1} - e_j = (\gamma-1)\beta e_j\beta^{-1} + (\beta e_j\beta^{-1} - e_j)$, and
$\beta e_j\beta^{-1} - e_j$ is read off the conjugation matrix `conjGL β` (trace zero part). For the converse,
`re_ne_zero_of_conjGL_mem_ballOne`, `mem_latP_of_conjMat_mem_ballOne` and `mem_lamCong_iff`.

Source: Weil 1982, §3.7, p. 65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.QuatOneAdd
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqLocal

open Matrix NumberField IsDedekindDomain WithZero MeasureTheory Set
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LerayPadic

/-! ### Coordinates -/

section Coord

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] {A B : K}

theorem qSmall_iff_qVec {r : ℤᵐ⁰} (z : ℍ[K,A,B]) : QSmall r z ↔ ∀ i : Fin 4, Valued.v (qVec z i) ≤ r := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i; fin_cases i <;> assumption
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩

theorem qVec_sub (x y : ℍ[K,A,B]) : qVec (x - y) = qVec x - qVec y := by
  funext i; fin_cases i <;> rfl

theorem re_mul_comm (x y : ℍ[K,A,B]) : (x * y).re = (y * x).re := by
  simp only [QuaternionAlgebra.re_mul]; ring

theorem re_conj (α : (ℍ[K,A,B])ˣ) (z : ℍ[K,A,B]) : ((α : ℍ[K,A,B]) * z * ((α⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])).re = z.re := by
  rw [re_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

/-- The basis quaternion $e_j$ ($e_0 = 1$, $e_1 = i$, $e_2 = j$, $e_3 = k$). -/
abbrev e4 (j : Fin 4) : ℍ[K,A,B] := vecQ (Pi.single j 1)

theorem e4_succ (j : Fin 3) : (e4 j.succ : ℍ[K,A,B]) = Quat.pure (Pi.single j 1) := by
  fin_cases j <;> ext <;> simp [vecQ, Quat.pure]

theorem e4_zero : (e4 0 : ℍ[K,A,B]) = 1 := by ext <;> simp [vecQ]

end Coord

/-! ### $K_m$ in terms of quaternions -/

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)
local notation "HV" => (QuatV (a : F) (b : F) v)

variable (ha0 : (a : F) ≠ 0)

/-- **$\phi(\alpha,\beta)\in K_m$ iff $\alpha e_j\beta^{-1}\equiv e_j\bmod\pi^m\Lambda_v$ for all $j$.** -/
theorem sqSOK_mem_ballOne_iff (m : ℕ) (p : sqPair Av Bv) :
    omat (sqSOK Fv ha0 p : orthGroup QF Fv) ∈ ballOne v m ↔
      ∀ j : Fin 4, QSmall (exp (-(m : ℤ))) (((p : HK Fv a b × HK Fv a b).1 : HV) * e4 j *
        ((((p : HK Fv a b × HK Fv a b).2)⁻¹ : HK Fv a b) : HV) - e4 j) := by
  have hcol : ∀ i j, omat (sqSOK Fv ha0 p : orthGroup QF Fv) i j - (1 : Matrix (Fin 4) (Fin 4) Fv) i j =
      qVec (((p : HK Fv a b × HK Fv a b).1 : HV) * e4 j *
        ((((p : HK Fv a b × HK Fv a b).2)⁻¹ : HK Fv a b) : HV) - e4 j) i := by
    intro i j
    have h := congrFun (sqSOK_mulVec ha0 p (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h
    rw [qVec_sub, Pi.sub_apply, ← h, qVec_vecQ]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  constructor
  · intro h j
    rw [qSmall_iff_qVec]
    intro i
    rw [← hcol]
    exact h i j
  · intro h i j
    rw [hcol]
    exact (qSmall_iff_qVec _).1 (h j) i

/-- **`conjGL β` $\in1+\pi^mM_3$ iff $\beta e_j\beta^{-1}\equiv e_j$ for the pure basis vectors.** -/
theorem conjGL_mem_ballOne_iff (m : ℕ) (β : HK Fv a b) :
    ((conjGL β : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m ↔
      ∀ j : Fin 3, QSmall (exp (-(m : ℤ))) ((β : HV) * e4 j.succ * ((β⁻¹ : HK Fv a b) : HV) - e4 j.succ) := by
  have hcol : ∀ (i j : Fin 3), ((conjGL β : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) i j -
      (1 : Matrix (Fin 3) (Fin 3) Fv) i j =
      qVec ((β : HV) * e4 j.succ * ((β⁻¹ : HK Fv a b) : HV) - e4 j.succ) i.succ := by
    intro i j
    have h : ((conjGL β : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) i j = conjLin β (Pi.single j 1) i := by
      rw [← conjGL_mulVec, Matrix.mulVec_single_one]; rfl
    rw [h, e4_succ, qVec_sub, Pi.sub_apply]
    simp only [conjLin, LinearMap.coe_mk, AddHom.coe_mk]
    fin_cases i <;> simp [qVec, imv, Quat.pure, Matrix.one_apply, Pi.single_apply, eq_comm]
  have hre : ∀ j : Fin 3, ((β : HV) * e4 j.succ * ((β⁻¹ : HK Fv a b) : HV) - e4 j.succ).re = 0 := by
    intro j
    rw [QuaternionAlgebra.re_sub, re_conj, e4_succ]; simp [Quat.pure]
  constructor
  · intro h j
    rw [qSmall_iff_qVec]
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change Valued.v ((β : HV) * e4 j.succ * ((β⁻¹ : HK Fv a b) : HV) - e4 j.succ).re ≤ _
      rw [hre j, map_zero]; exact zero_le'
    · rw [← hcol]; exact h i j
  · intro h i j
    rw [hcol]
    exact (qSmall_iff_qVec _).1 (h j) i.succ

theorem qSmall_one_e4 (j : Fin 4) : QSmall (1 : ℤᵐ⁰) (e4 j : HV) := by
  rw [qSmall_iff_qVec]; intro i
  simp only [qVec_vecQ, Pi.single_apply]
  split_ifs <;> simp

theorem qSmall_one_of_lamLocUnits {u : HK Fv a b} (hu : u ∈ lamLocUnits (a : F) (b : F) v) :
    QSmall (1 : ℤᵐ⁰) (u : HV) ∧ QSmall (1 : ℤᵐ⁰) ((u⁻¹ : HK Fv a b) : HV) :=
  ⟨(qSmall_one_iff_mem_lamLoc v a b _).2 hu.1, (qSmall_one_iff_mem_lamLoc v a b _).2 hu.2⟩

/-- **$\phi(\alpha,\beta)\in K_m$ for $\beta\in\Lambda^{(m)}_v$, $\alpha\beta^{-1}\in1+\pi^m\Lambda_v$.** -/
theorem sqSOK_mem_congSub (m : ℕ) (hm : 1 ≤ m) (p : sqPair Av Bv)
    (hβ : (p : HK Fv a b × HK Fv a b).2 ∈ lamCong v a b m hm)
    (hγ : (p : HK Fv a b × HK Fv a b).1 * ((p : HK Fv a b × HK Fv a b).2)⁻¹ ∈ oneAddCong v a b m) :
    (sqSOK Fv ha0 p : orthGroup QF Fv) ∈ congSub v Q₀ m hm := by
  rw [mem_congSub]
  refine (sqSOK_mem_ballOne_iff ha0 m p).2 fun j => ?_
  set α := (p : HK Fv a b × HK Fv a b).1
  set β := (p : HK Fv a b × HK Fv a b).2
  set γ := α * β⁻¹ with hγdef
  have hA := valuedA v a
  have hB := valuedB v b
  have hβ1 := qSmall_one_of_lamLocUnits hβ.2
  have hconj : QSmall (1 : ℤᵐ⁰) ((β : HV) * e4 j * ((β⁻¹ : HK Fv a b) : HV)) :=
    QSmall.mul_left hA hB (QSmall.mul_left hA hB hβ1.1 (qSmall_one_e4 j)) hβ1.2
  have hsplit : (α : HV) * e4 j * ((β⁻¹ : HK Fv a b) : HV) - e4 j =
      ((γ : HV) - 1) * ((β : HV) * e4 j * ((β⁻¹ : HK Fv a b) : HV)) +
        ((β : HV) * e4 j * ((β⁻¹ : HK Fv a b) : HV) - e4 j) := by
    have hα : (α : HV) = (γ : HV) * (β : HV) := by
      rw [hγdef, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [hα]; noncomm_ring
  rw [hsplit]
  refine (hγ.2.mul_right hA hB hconj).add ?_
  -- the conjugation part, from `β ∈ Λ^{(m)}_v`
  have hX : ((conjGL β : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := hβ.1
  refine Fin.cases ?_ (fun j' => ?_) j
  · rw [e4_zero, mul_one, Units.mul_inv, sub_self]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  · exact (conjGL_mem_ballOne_iff m β).1 hX j'

/-- **Conversely**, $\phi(\alpha,\beta)\in K_m$ ($2s < m$, $s + e_a\le m$) gives $c$ with $c\beta\in\Lambda^{(m)}_v$, and
$\alpha\beta^{-1}\in1+\pi^m\Lambda_v$. -/
theorem exists_smul_of_sqSOK_mem_congSub {s eA m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hAe : Valued.v Av = exp (-(eA : ℤ))) (h2s : 2 * s < m) (hmA : s + eA ≤ m) (hm : 1 ≤ m) (p : sqPair Av Bv)
    (hp : (sqSOK Fv ha0 p : orthGroup QF Fv) ∈ congSub v Q₀ m hm) :
    (p : HK Fv a b × HK Fv a b).1 * ((p : HK Fv a b × HK Fv a b).2)⁻¹ ∈ oneAddCong v a b m ∧
      ∃ r : Fvˣ, Units.map (algebraMap Fv HV).toMonoidHom r * (p : HK Fv a b × HK Fv a b).2 ∈
        lamCong v a b m hm := by
  rw [mem_congSub] at hp
  have hcols := (sqSOK_mem_ballOne_iff ha0 m p).1 hp
  set α := (p : HK Fv a b × HK Fv a b).1
  set β := (p : HK Fv a b × HK Fv a b).2
  have hA := valuedA v a
  have hB := valuedB v b
  have hγ : α * β⁻¹ ∈ oneAddCong v a b m := by
    rw [mem_oneAddCong_iff v a b hm]
    have := hcols 0
    rwa [e4_zero, mul_one, ← Units.val_mul] at this
  refine ⟨hγ, ?_⟩
  set γ := α * β⁻¹ with hγdef
  have hγi : γ⁻¹ ∈ oneAddCong v a b m := (oneAddCong v a b m).inv_mem hγ
  have hγi1 := qSmall_one_of_lamLocUnits hγi.1
  -- the conjugation matrix of `β`
  have hX : ((conjGL β : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := by
    refine (conjGL_mem_ballOne_iff m β).2 fun j => ?_
    have hsplit : (β : HV) * e4 j.succ * ((β⁻¹ : HK Fv a b) : HV) - e4 j.succ =
        ((γ⁻¹ : HK Fv a b) : HV) * ((α : HV) * e4 j.succ * ((β⁻¹ : HK Fv a b) : HV) - e4 j.succ) +
          (((γ⁻¹ : HK Fv a b) : HV) - 1) * e4 j.succ := by
      have hβ' : (β : HV) = ((γ⁻¹ : HK Fv a b) : HV) * (α : HV) := by
        rw [hγdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
      rw [hβ']; noncomm_ring
    rw [hsplit]
    exact (QSmall.mul_left hA hB hγi1.1 (hcols j.succ)).add (hγi.2.mul_right hA hB (qSmall_one_e4 _))
  have hr0 : (β : HV).re ≠ 0 := re_ne_zero_of_conjGL_mem_ballOne hs h2s β hX
  refine ⟨Units.mk0 ((β : HV).re)⁻¹ (inv_ne_zero hr0), ?_⟩
  set w := Units.map (algebraMap Fv HV).toMonoidHom (Units.mk0 ((β : HV).re)⁻¹ (inv_ne_zero hr0)) * β
  have hw := scale_val Av Bv β hr0
  have hwX : ((conjGL w : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := by
    rw [conjGL_smul]; exact hX
  have hy := mem_latP_of_conjMat_mem_ballOne hA hB hs (by omega) w hw hwX
  rw [mem_lamCong_iff v a b hs hAe h2s hmA hm]
  refine ⟨?_, ?_⟩
  · rw [hw]; simp [Quat.pure]
  · rw [hw]; simpa [imv, Quat.pure] using hy

end Local

end QuadFormsKB.Tamagawa.Measure.Weil
