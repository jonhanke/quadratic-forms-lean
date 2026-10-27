/-
# The local-global principle for representations of forms, and vanishing when $V$ does not represent $T$

**Layer:** $F$ a totally real number field; $Q_0$ of rank $N$ and $T_0$ of rank $r$ totally positive definite forms over $\mathcal O_F$;
$F_v$ the completion at a finite prime $v$. A form $Q$ *represents* $T$ over a field $K$ if $Q(X\vec y) = T(\vec y)$ for some
$X \in K^{N\times r}$ (equivalently $Q\circ X = T$, `compMat_map_iff`, `compMat_iff_self`).

**Proves**
* `exists_local_not_rep` (**the local-global principle for representations of forms**, O'Meara 1963, 66:3 [unverified for forms]):
  if $Q_0$ does not represent $T_0$ over $F$, then for some finite prime $v$ it does not over $F_v$ (the real places never obstruct, since
  $Q_0$ is totally positive definite and the numbers represented are totally positive). Proof by induction on $r$ (`rep_of_local_diag`):
  diagonalize $Q \cong \langle a_0, \dots\rangle$ and $T \cong \langle d_0, \dots, d_{r-1}\rangle$ over $F$; the number $d_0$ is represented
  everywhere locally (finite places by hypothesis, real places by total positivity), hence over $F$ by Hasse-Minkowski for numbers
  (`represents_iff_everywhere_nf`); split $\langle a\rangle \cong \langle d_0\rangle \perp \langle\alpha\rangle$ over $F$ (`exists_isometric_diag_cons`),
  and cancel $\langle d_0\rangle$ locally by Witt (`rep_step`: the first column $x_0$ of a representation completes to an orthogonal basis,
  `exists_iso_cons`), so $\langle\alpha\rangle$ represents $\langle d_1,\dots\rangle$ at every finite place, with $\alpha$ again totally positive; apply the induction hypothesis
  and reassemble (`rep_cons`).
* `localDensityForm_eq_zero_of_not_rep`: no solution over $F_v$ forces $\beta_\mathfrak p(Q_0, T_0) = 0$ ($r \le N$, $T_0$ nondegenerate):
  a nonzero density gives a solution mod $\pi^{2d+1}$, which Hensel for frames (`exists_formF_eq_of_dvd`) lifts to an exact solution
  over $\mathfrak o_\mathfrak p \subseteq F_\mathfrak p$.
* `repMassT_eq_zero_of_not_rep`: if $Q$ does not represent $T$ over $F$, then $\mathrm{repMass}_T(L) = 0$ for every lattice $L$.
* `tprod_siegelDensity_eq_zero_of_not_rep`: then $\prod_\mathfrak p \alpha_\mathfrak p(Q_0, T_0) = 0$ ($r \le N$).

**Sources.** O'Meara 1963, 66:3 (local-global for representations of numbers; Hasse-Minkowski); Hensel lifting for frames (Kitaoka 1993, §5.6
[unverified]); Witt cancellation (Lam I; Serre IV). Indices are 0-based: $T = \langle d_0, \dots, d_{r-1}\rangle$.
The positivity hypotheses are `Lattices.IsTotallyPosDef` of the base changes to $F$.
-/
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Literature.HasseNorm.Infinite
import QuadFormsKB.Tamagawa.TernaryReduction
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.LocalDensity.NFFormDensity
import QuadFormsKB.Tamagawa.FrameHensel
import QuadFormsKB.Tamagawa.FrameRepMass
import QuadFormsKB.Tamagawa.MassInduction

open Matrix NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

section DiagStep

variable {K : Type*} [Field K] [CharZero K]

theorem evalIn_diag_cons {m : ℕ} (b : K) (α : Fin m → K) (v : Fin (m + 1) → K) :
    (QuadForm.diag (Fin.cons b α : Fin (m + 1) → K)).evalIn K v =
      b * v 0 ^ 2 + (QuadForm.diag α).evalIn K (Fin.tail v) := by
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag, Fin.sum_univ_succ]
  simp [Fin.tail]

theorem exists_iso_cons {n : ℕ} (Q : QuadForm K (n + 1)) (hQ : Q.Nondegenerate)
    {x : Fin (n + 1) → K} {b : K} (hb : b ≠ 0) (hx : Q.evalIn K x = b) :
    ∃ (α : Fin n → K) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) K), (∀ i, α i ≠ 0) ∧ IsUnit P.det ∧
      P *ᵥ Pi.single 0 1 = x ∧
      ∀ z, Q.evalIn K (P *ᵥ z) = (QuadForm.diag (Fin.cons b α : Fin (n + 1) → K)).evalIn K z := by
  classical
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hwo, hw0⟩ := QuadForm.exists_orthogonal_basis_cons (QuadForm.halfBilin_isSymm Q)
    (x := x) (by rw [QuadForm.halfBilin_self, hx]; exact hb) (Module.finrank_fin_fun K)
  have hwo' : ∀ i j, i ≠ j → Q.halfBilin (w i) (w j) = 0 := fun i j hij => hwo hij
  obtain ⟨hne, -⟩ := QuadForm.isometric_diag_of_basis Q hQ w hwo'
  have hdiag : (fun i => Q.evalIn K (w i)) = (Fin.cons b (fun i : Fin n => Q.evalIn K (w i.succ)) :
      Fin (n + 1) → K) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [hw0, hx]
    · simp
  refine ⟨fun i => Q.evalIn K (w i.succ), (Pi.basisFun K (Fin (n + 1))).toMatrix w,
    fun i => hne _, ?_, ?_, ?_⟩
  · rw [← Module.Basis.det_apply]; exact Module.Basis.isUnit_det _ _
  · rw [← hw0]
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Pi.single_apply]
  · intro z
    have hmv : ((Pi.basisFun K (Fin (n + 1))).toMatrix w).mulVec z = ∑ j, z j • w j := by
      funext i
      simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
    rw [← hdiag, ← QuadForm.halfBilin_self, hmv, QuadForm.evalIn_diag]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i, ← QuadForm.halfBilin_self]
    · simp; ring
    · intro j _ hj; simp [hwo' j i hj]
    · simp

theorem rep_step {m r : ℕ} {b : K} (hb : b ≠ 0) {α : Fin m → K} (hα : ∀ i, α i ≠ 0) {δ : Fin r → K}
    (X : Matrix (Fin (m + 1)) (Fin (r + 1)) K)
    (hX : ∀ y, (QuadForm.diag (Fin.cons b α : Fin (m + 1) → K)).evalIn K (X *ᵥ y) =
      (QuadForm.diag (Fin.cons b δ : Fin (r + 1) → K)).evalIn K y) :
    ∃ Y : Matrix (Fin m) (Fin r) K,
      ∀ y, (QuadForm.diag α).evalIn K (Y *ᵥ y) = (QuadForm.diag δ).evalIn K y := by
  classical
  set Q := QuadForm.diag (Fin.cons b α : Fin (m + 1) → K) with hQ
  have hQnd : Q.Nondegenerate := by
    have : ∀ i, (Fin.cons b α : Fin (m + 1) → K) i ≠ 0 := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hb
      · simpa using hα i
    exact QuadForm.nondegenerate_diag this
  set x := X *ᵥ Pi.single 0 1 with hxdef
  have hx : Q.evalIn K x = b := by
    rw [hxdef, hX, evalIn_diag_cons]
    simp [QuadForm.evalIn_diag, Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
  obtain ⟨α', P, hα', hPu, hP0, hPQ⟩ := exists_iso_cons Q hQnd hb hx
  have h1 : (QuadForm.diag (Fin.cons b α' : Fin (m + 1) → K)).IsometricIn K Q :=
    QuadForm.isometricIn_symm K ⟨P, hPu, hPQ⟩
  have h2 := QuadForm.isometricIn_symm K (QuadForm.isometricIn_of_diag_cons K hb hα' h1)
  obtain ⟨R, -, hR⟩ := h2
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  set Φ := P⁻¹ * X with hΦdef
  have hΦ : ∀ y, (QuadForm.diag (Fin.cons b α' : Fin (m + 1) → K)).evalIn K (Φ *ᵥ y) =
      (QuadForm.diag (Fin.cons b δ : Fin (r + 1) → K)).evalIn K y := by
    intro y
    rw [← hPQ, Matrix.mulVec_mulVec, hΦdef, ← Matrix.mul_assoc, hPinv, Matrix.one_mul, hX]
  have hΦ0 : Φ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [hΦdef, ← Matrix.mulVec_mulVec, ← hxdef, ← hP0, Matrix.mulVec_mulVec, hPinv', Matrix.one_mulVec]
  have key : ∀ y' : Fin r → K, ∃ Y' : Fin m → K,
      (QuadForm.diag α').evalIn K Y' = (QuadForm.diag δ).evalIn K y' ∧
      Y' = fun i => (Φ *ᵥ (Fin.cons 0 y' : Fin (r + 1) → K)) i.succ := by
    intro y'
    set u := Φ *ᵥ (Fin.cons 0 y' : Fin (r + 1) → K) with hu
    have hs : ∀ s : K, b * (s + u 0) ^ 2 + (QuadForm.diag α').evalIn K (Fin.tail u) =
        b * s ^ 2 + (QuadForm.diag δ).evalIn K y' := by
      intro s
      have hcons : (Fin.cons s y' : Fin (r + 1) → K) = s • (Pi.single 0 1 : Fin (r + 1) → K) +
          (Fin.cons 0 y' : Fin (r + 1) → K) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp
        · simp [Pi.single_apply, Fin.succ_ne_zero]
      have := hΦ (Fin.cons s y')
      rw [hcons, Matrix.mulVec_add, Matrix.mulVec_smul, hΦ0, ← hu, evalIn_diag_cons,
        evalIn_diag_cons] at this
      have t1 : Fin.tail (s • (Pi.single 0 1 : Fin (m + 1) → K) + u) = Fin.tail u := by
        funext i; simp [Fin.tail, Fin.succ_ne_zero]
      have t2 : Fin.tail (s • (Pi.single 0 1 : Fin (r + 1) → K) + (Fin.cons 0 y' : Fin (r + 1) → K))
          = y' := by
        funext i; simp [Fin.tail, Fin.succ_ne_zero]
      rw [t1, t2] at this
      simpa using this
    have h0 := hs 0
    have h1' := hs 1
    have hu0 : u 0 = 0 := by
      have : b * (2 * u 0) = 0 := by linear_combination h1' - h0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hb
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h two_ne_zero
        · exact h
    refine ⟨Fin.tail u, ?_, rfl⟩
    rw [hu0] at h0
    simpa using h0
  let Y0 : Matrix (Fin m) (Fin r) K := Matrix.of fun i j => Φ i.succ j.succ
  refine ⟨R * Y0, fun y' => ?_⟩
  obtain ⟨Y', hY', hY'e⟩ := key y'
  have hmv : Y0 *ᵥ y' = Y' := by
    rw [hY'e]
    funext i
    simp [Y0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [← Matrix.mulVec_mulVec, hmv, hR, hY']

end DiagStep

/-! ### Representation of forms, transfer along isometries, and the base-change bridges -/

section RepSec

open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [CharZero F]

/-- **$Q$ represents $T$ over $K$:** a matrix $X \in K^{N\times r}$ with $Q(X\vec y) = T(\vec y)$ for all $\vec y \in K^r$. -/
def Rep (K : Type) [Field K] [Algebra F K] {N r : ℕ} (Q : QuadForm F N) (T : QuadForm F r) : Prop :=
  ∃ X : Matrix (Fin N) (Fin r) K, ∀ y, Q.evalIn K (X *ᵥ y) = T.evalIn K y

variable {K : Type} [Field K] [Algebra F K] {N r : ℕ}

theorem rep_of_iso_left {Q Q' : QuadForm F N} {T : QuadForm F r} (h : Q.IsometricIn K Q')
    (hr : Rep K Q' T) : Rep K Q T := by
  obtain ⟨P, -, hP⟩ := h
  obtain ⟨X, hX⟩ := hr
  exact ⟨P * X, fun y => by rw [← Matrix.mulVec_mulVec, hP, hX]⟩

theorem rep_of_iso_right {Q : QuadForm F N} {T T' : QuadForm F r} (h : T.IsometricIn K T')
    (hr : Rep K Q T) : Rep K Q T' := by
  obtain ⟨P, -, hP⟩ := h
  obtain ⟨X, hX⟩ := hr
  exact ⟨X * P, fun y => by rw [← Matrix.mulVec_mulVec, hX, hP]⟩

theorem evalIn_diag_base (K : Type) [Field K] [Algebra F K] {n : ℕ} (a : Fin n → F) (z : Fin n → K) :
    (QuadForm.diag a).evalIn K z = (QuadForm.diag (fun i => algebraMap F K (a i))).evalIn K z := by
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
  simp

theorem rep_iff_diag {Q : QuadForm F N} {a : Fin N → F} {T : QuadForm F r} {t : Fin r → F}
    (hQ : Q.IsometricIn F (QuadForm.diag a)) (hT : T.IsometricIn F (QuadForm.diag t)) (K : Type)
    [Field K] [Algebra F K] : Rep K Q T ↔ Rep K (QuadForm.diag a) (QuadForm.diag t) := by
  have hQK := FieldGen.isometricIn_of_base K hQ
  have hTK := FieldGen.isometricIn_of_base K hT
  constructor
  · intro h
    exact rep_of_iso_right hTK (rep_of_iso_left (QuadForm.isometricIn_symm K hQK) h)
  · intro h
    exact rep_of_iso_right (QuadForm.isometricIn_symm K hTK) (rep_of_iso_left hQK h)

theorem evalIn_eq_eval_map_alg {n : ℕ} (Q : QuadForm F n) (z : Fin n → K) :
    Q.evalIn K z = (Q.map (algebraMap F K)).eval z := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- **Matrix equality of forms versus representation:** $(Q \otimes K)\circ X = T \otimes K$ iff $Q(X\vec y) = T(\vec y)$ for all $\vec y$. -/
theorem compMat_map_iff (Q : QuadForm F N) (T : QuadForm F r) (X : Matrix (Fin N) (Fin r) K) :
    (Q.map (algebraMap F K)).compMat X = T.map (algebraMap F K) ↔
      ∀ y, Q.evalIn K (X *ᵥ y) = T.evalIn K y := by
  constructor
  · intro h y
    rw [evalIn_eq_eval_map_alg, evalIn_eq_eval_map_alg, ← h, QuadForm.eval_compMat]
  · intro h
    refine QuadForm.eq_of_eval_eq fun y => ?_
    rw [QuadForm.eval_compMat, ← evalIn_eq_eval_map_alg, ← evalIn_eq_eval_map_alg]
    exact h y

theorem compMat_iff_self (Q : QuadForm F N) (T : QuadForm F r) (X : Matrix (Fin N) (Fin r) F) :
    Q.compMat X = T ↔ ∀ y, Q.evalIn F (X *ᵥ y) = T.evalIn F y := by
  constructor
  · intro h y
    rw [← h]
    exact (QuadForm.eval_compMat Q X y).symm
  · intro h
    refine QuadForm.eq_of_eval_eq fun y => ?_
    exact (QuadForm.eval_compMat Q X y).trans (h y)

end RepSec

/-! ### The local-global principle for diagonal forms, by induction on the rank of $T$ -/

section LocalGlobal

open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Totally positive:** $\sigma(x) > 0$ at every (real) place $\sigma$ of the totally real field $F$. -/
def Pos (x : F) : Prop := ∀ v : InfinitePlace F, 0 < realEmb F v x

theorem Pos.ne_zero {x : F} (hx : Pos x) : x ≠ 0 := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have := hx w
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem pos_diag_eval {n : ℕ} {a : Fin n → F} (ha : ∀ i, Pos (a i)) {x : Fin n → F} (hx : x ≠ 0) :
    Pos ((QuadForm.diag a).evalIn F x) := by
  intro v
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  rw [QuadForm.evalIn_diag]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, map_sum, map_mul, map_pow]
  refine Finset.sum_pos' (fun i _ => mul_nonneg (ha i v).le (sq_nonneg _)) ⟨j, Finset.mem_univ _, ?_⟩
  exact mul_pos (ha j v) (pow_pos_of_ne_zero' hj v)
where
  pow_pos_of_ne_zero' {z : F} (hz : z ≠ 0) (v : InfinitePlace F) : 0 < realEmb F v z ^ 2 := by
    have : realEmb F v z ≠ 0 := (map_ne_zero _).mpr (by simpa using hz)
    positivity

/-- A totally positive definite form represents every totally positive $\rho$ over a real completion, if
its first diagonal entry is totally positive. -/
theorem rep_real {n : ℕ} (a : Fin (n + 1) → F) (ha : Pos (a 0)) {ρ : F} (hρ : Pos ρ)
    (w : InfinitePlace F) : (QuadForm.diag a).RepresentsIn w.Completion ρ := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have he : ∀ c : F, e (algebraMap F w.Completion c) = realEmb F w c := fun c => by
    rw [QuadFormsKB.HN.real_algebraMap hw c]; rfl
  set t : w.Completion := e.symm (Real.sqrt (realEmb F w ρ / realEmb F w (a 0)))
  refine ⟨t • Pi.single 0 1, ?_⟩
  apply e.injective
  have hev : (QuadForm.diag a).evalIn w.Completion (t • (Pi.single 0 1 : Fin (n + 1) → w.Completion)) =
      algebraMap F w.Completion (a 0) * t ^ 2 := by
    rw [QuadForm.evalIn_diag, Finset.sum_eq_single 0]
    · simp [Pi.single_apply]
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  rw [hev, map_mul, map_pow, he, he]
  simp only [t, RingEquiv.apply_symm_apply]
  rw [Real.sq_sqrt (div_nonneg (hρ w).le (ha w).le), mul_div_cancel₀ _ (ha w).ne']

theorem rep_represents {K : Type} [Field K] [Algebra F K] {N r : ℕ} (a : Fin N → F) (d : Fin (r + 1) → F)
    (h : Rep K (QuadForm.diag a) (QuadForm.diag d)) : (QuadForm.diag a).RepresentsIn K (d 0) := by
  obtain ⟨X, hX⟩ := h
  refine ⟨X *ᵥ Pi.single 0 1, ?_⟩
  rw [hX, QuadForm.evalIn_diag, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

theorem rep_cons {N r : ℕ} (b : F) (α : Fin N → F) (dt : Fin r → F)
    (h : Rep F (QuadForm.diag α) (QuadForm.diag dt)) :
    Rep F (QuadForm.diag (Fin.cons b α : Fin (N + 1) → F)) (QuadForm.diag (Fin.cons b dt : Fin (r + 1) → F)) := by
  obtain ⟨Y, hY⟩ := h
  let X : Matrix (Fin (N + 1)) (Fin (r + 1)) F := Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => Y i' j') j) i
  refine ⟨X, fun y => ?_⟩
  have hX : X *ᵥ y = (Fin.cons (y 0) (Y *ᵥ Fin.tail y) : Fin (N + 1) → F) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [X, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · simp [X, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]
  rw [hX, evalIn_diag_cons, evalIn_diag_cons]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [hY]

theorem alg_cons {K : Type} [Field K] [Algebra F K] {n : ℕ} (b : F) (α : Fin n → F) :
    (fun i => algebraMap F K ((Fin.cons b α : Fin (n + 1) → F) i)) =
      (Fin.cons (algebraMap F K b) (fun i => algebraMap F K (α i)) : Fin (n + 1) → K) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- **Cancelling the first entry locally** (Witt cancellation, `rep_step`): if $\langle a \rangle \cong \langle d_0, \alpha \rangle$ over $F$
and $\langle a \rangle$ represents $\langle d_0, d_t \rangle$ over a field $K \supseteq F$, then $\langle \alpha \rangle$ represents $\langle d_t \rangle$ over $K$. -/
theorem rep_local_step {K : Type} [Field K] [Algebra F K] {n r : ℕ} (d0 : F) (hd0 : d0 ≠ 0)
    (α : Fin n → F) (hα : ∀ i, α i ≠ 0) (dt : Fin r → F) (a : Fin (n + 1) → F)
    (hiso : (QuadForm.diag a).IsometricIn F (QuadForm.diag (Fin.cons d0 α : Fin (n + 1) → F)))
    (h : Rep K (QuadForm.diag a) (QuadForm.diag (Fin.cons d0 dt : Fin (r + 1) → F))) :
    Rep K (QuadForm.diag α) (QuadForm.diag dt) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have h1 := rep_of_iso_left (K := K)
    (QuadForm.isometricIn_symm K (FieldGen.isometricIn_of_base K hiso)) h
  obtain ⟨X, hX⟩ := h1
  have hX' : ∀ y, (QuadForm.diag (Fin.cons (algebraMap F K d0) (fun i => algebraMap F K (α i)) :
      Fin (n + 1) → K)).evalIn K (X *ᵥ y) =
      (QuadForm.diag (Fin.cons (algebraMap F K d0) (fun i => algebraMap F K (dt i)) :
        Fin (r + 1) → K)).evalIn K y := by
    intro y
    have e1 := evalIn_diag_base K (Fin.cons d0 α : Fin (n + 1) → F) (X *ᵥ y)
    have e2 := evalIn_diag_base K (Fin.cons d0 dt : Fin (r + 1) → F) y
    rw [alg_cons] at e1 e2
    exact e1.symm.trans ((hX y).trans e2)
  obtain ⟨Y, hY⟩ := rep_step ((map_ne_zero _).mpr hd0) (fun i => (map_ne_zero _).mpr (hα i)) X hX'
  exact ⟨Y, fun y => (evalIn_diag_base K α _).trans ((hY y).trans (evalIn_diag_base K dt y).symm)⟩

/-- **Local-global principle for diagonal forms** (O'Meara 1963, 66:3 for a single number; here by induction on
the rank $r$ of the represented form $\langle d_0, \dots, d_{r-1}\rangle$): if $\langle a_0, \dots, a_{N-1}\rangle$ and
$\langle d_0, \dots, d_{r-1}\rangle$ have totally positive entries, and the first represents the second over $F_v$ for
every finite $v$, then it does so over $F$. -/
theorem rep_of_local_diag (r : ℕ) : ∀ (N : ℕ) (a : Fin N → F) (d : Fin r → F), (∀ i, Pos (a i)) →
    (∀ j, Pos (d j)) → (∀ v : HeightOneSpectrum (𝓞 F), Rep (v.adicCompletion F) (QuadForm.diag a) (QuadForm.diag d)) →
      Rep F (QuadForm.diag a) (QuadForm.diag d) := by
  induction r with
  | zero =>
    intro N a d _ _ _
    exact ⟨0, fun y => by simp [QuadForm.evalIn_diag]⟩
  | succ r ih =>
    intro N a d ha hd hloc
    obtain ⟨d0, dt, rfl⟩ : ∃ d0 dt, d = (Fin.cons d0 dt : Fin (r + 1) → F) :=
      ⟨d 0, Fin.tail d, (Fin.cons_self_tail d).symm⟩
    have hd0 : Pos d0 := by simpa using hd 0
    have hdt : ∀ j, Pos (dt j) := fun j => by simpa using hd j.succ
    have hd0ne : d0 ≠ 0 := hd0.ne_zero
    obtain ⟨v₀⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := inferInstance
    cases N with
    | zero =>
      exfalso
      obtain ⟨x, hx⟩ := rep_represents a _ (hloc v₀)
      simp only [Fin.cons_zero] at hx
      rw [QuadForm.evalIn_diag] at hx
      simp at hx
      exact hd0ne ((map_eq_zero _).mp hx.symm)
    | succ n =>
      have hane : ∀ i, a i ≠ 0 := fun i => (ha i).ne_zero
      have hnd := QuadForm.nondegenerate_diag hane
      have hrepF : (QuadForm.diag a).RepresentsIn F d0 := by
        rw [represents_iff_everywhere_nf (QuadForm.diag a) hnd d0 hd0ne]
        intro p
        cases p with
        | infinite w => exact rep_real a (ha 0) hd0 w
        | finite v =>
          show (QuadForm.diag a).RepresentsIn (v.adicCompletion F) d0
          simpa using rep_represents a _ (hloc v)
      obtain ⟨α, hα, hiso'⟩ := QuadForm.exists_isometric_diag_cons hnd hd0ne hrepF
      obtain ⟨P, hPu, hP⟩ := id hiso'
      have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
      have hαpos : ∀ i, Pos (α i) := by
        intro i
        have hne : P *ᵥ (Pi.single i.succ 1 : Fin (n + 1) → F) ≠ 0 := by
          intro h
          have h2 := congrArg (fun z => P⁻¹ *ᵥ z) h
          simp only [Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
          have := congrFun h2 i.succ
          simp at this
        have := pos_diag_eval ha hne
        rw [hP, QuadForm.evalIn_diag, Finset.sum_eq_single i.succ] at this
        · simpa using this
        · intro j _ hj; simp [Pi.single_apply, hj]
        · simp
      have hlocα : ∀ v : HeightOneSpectrum (𝓞 F),
          Rep (v.adicCompletion F) (QuadForm.diag α) (QuadForm.diag dt) := by
        intro v
        exact rep_local_step d0 hd0ne α hα dt a hiso' (hloc v)
      exact rep_of_iso_left hiso' (rep_cons d0 α dt (ih n α dt hαpos hdt hlocα))

theorem pos_of_isTotallyPos {x : F} (hx : Lattices.IsTotallyPos x) : Pos x := fun v =>
  LatChange.realEmb_pos_of_isTotallyPos hx v

theorem mulVec_ne_zero_of_isUnit {n : ℕ} {P : Matrix (Fin n) (Fin n) F} (hP : IsUnit P.det)
    {x : Fin n → F} (hx : x ≠ 0) : P *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have h2 := congrArg (fun z => P⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec,
    Matrix.mulVec_zero] using h2

theorem evalIn_diag_single {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (QuadForm.diag a).evalIn F (Pi.single i 1) = a i := by
  rw [QuadForm.evalIn_diag, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

/-- **Local-global principle for representations of forms over $F$** (O'Meara 1963, 66:3, by induction on the rank of
$T$; Hasse–Minkowski for numbers `represents_iff_everywhere_nf` at each step): if $Q$ and $T$ are totally positive
definite over the totally real field $F$ and $Q$ represents $T$ over $F_v$ for every finite $v$, then $Q$ represents $T$ over $F$. -/
theorem rep_of_local_forms {N r : ℕ} (Q : QuadForm F N) (hQ : Lattices.IsTotallyPosDef Q)
    (T : QuadForm F r) (hT : Lattices.IsTotallyPosDef T)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), Rep (v.adicCompletion F) Q T) : Rep F Q T := by
  obtain ⟨a, -, hQa⟩ := FieldGen.exists_isometric_diag Q hQ.nondegenerate
  obtain ⟨t, -, hTt⟩ := FieldGen.exists_isometric_diag T hT.nondegenerate
  have hpos : ∀ {n : ℕ} (S : QuadForm F n) (hS : Lattices.IsTotallyPosDef S) (c : Fin n → F),
      S.IsometricIn F (QuadForm.diag c) → ∀ i, Pos (c i) := by
    intro n S hS c hSc i
    obtain ⟨P, hPu, hP⟩ := hSc
    have hne : P *ᵥ (Pi.single i 1 : Fin n → F) ≠ 0 :=
      mulVec_ne_zero_of_isUnit hPu (by
        intro h; have := congrFun h i; simp at this)
    have := pos_of_isTotallyPos (hS _ hne)
    rwa [show S.eval (P *ᵥ Pi.single i 1) = c i from (hP _).trans (evalIn_diag_single c i)] at this
  have h := rep_of_local_diag r N a t (hpos Q hQ a hQa) (hpos T hT t hTt)
    (fun v => (rep_iff_diag hQa hTt _).mp (hloc v))
  exact (rep_iff_diag hQa hTt F).mpr h

/-- **The local-global principle for representations of forms** (O'Meara 1963, 66:3; Hasse–Minkowski for numbers at
each step of an induction on $r$): let $F$ be totally real, and $Q_0$, $T_0$ totally positive definite over $\mathcal O_F$ (as
forms over $F$) of ranks $N$, $r$. If $Q_0$ does not represent $T_0$ over $F$ (no $X \in F^{N\times r}$ with $Q_0\circ X = T_0$),
then for some finite prime $v$ it does not over $F_v$.

(The totally positive definite hypothesis on $Q_0$ is what disposes of the real places.) -/
@[kb "omeara1963" "§66, 66:3, p. 189 (representations of forms; here by induction on the rank)"]
theorem exists_local_not_rep {N r : ℕ} (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hQ : Lattices.IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hT : Lattices.IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)) :
    ∃ v : HeightOneSpectrum (𝓞 F), ¬ ∃ X : Matrix (Fin N) (Fin r) (v.adicCompletion F),
      ((Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))).compMat X =
        (T₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F)) := by
  by_contra hall
  push Not at hall
  apply h
  obtain ⟨X, hX⟩ := rep_of_local_forms _ hQ _ hT (fun v => by
    obtain ⟨X, hX⟩ := hall v
    exact ⟨X, (compMat_map_iff _ _ X).mp hX⟩)
  exact ⟨X, (compMat_iff_self _ _ X).mpr hX⟩

end LocalGlobal

/-! ### Local densities vanish when there is no local representation -/

section Density

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

theorem Qp_map_eq (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (S : QuadForm (𝓞 F) m) :
    (NF.Qp v S).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      (S.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F)) := by
  ext i j
  rfl

/-- **No local representation forces a vanishing local density** (Hensel for frames, `exists_formF_eq_of_dvd`): if $T_0$ is
nondegenerate, $r \le N$ and there is no $X \in F_v^{N\times r}$ with $Q_0\circ X = T_0$, then
$\beta_\mathfrak p(Q_0, T_0) = 0$. (If $\beta_\mathfrak p \ne 0$, then $A_{\mathfrak p^k}(Q_0, T_0) \ne 0$ for $k = 2d+1$,
$\pi^d \,\Vert\, \det H_{T_0}$, so $Q_0\circ X \equiv T_0 \bmod \pi^k$ has a solution, which Hensel lifts to an exact one over
$\mathfrak o_\mathfrak p \subseteq F_\mathfrak p$.) -/
@[kb "kitaoka1993" "§5.6 (lifting representations) [unverified]"]
theorem localDensityForm_eq_zero_of_not_rep (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) N)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (hrN : r ≤ N)
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) (v.adicCompletion F),
      ((Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))).compMat X =
        (T₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))) :
    NF.localDensityForm v Q₀ T₀ = 0 := by
  by_contra hne
  have hπ := NF.irreducible_π v
  have hTo : (NF.Qp v T₀).Nondegenerate := NF.nondegenerate_Qp v hT
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hTo
  have hβ : NF.localDensityForm v Q₀ T₀ =
      (DVR.repCountForm (NF.Qp v Q₀) (NF.Qp v T₀) (NF.π v) (2 * d + 1) : ℝ) /
        (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ ((2 * d + 1) * (N * r - r * (r + 1) / 2)) := by
    rw [NF.localDensityForm_eq_completion]
    exact DVR.localDensityForm_eq _ _ _ hπ d hd hd' hrN _ le_rfl
  have hrep : DVR.repCountForm (NF.Qp v Q₀) (NF.Qp v T₀) (NF.π v) (2 * d + 1) ≠ 0 := by
    intro h0
    apply hne
    rw [hβ, h0]
    simp
  rw [DVR.repCountForm_eq_card_sol] at hrep
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hrep).1
  obtain ⟨y, hy, -⟩ := exists_formF_eq_of_dvd hπ (NF.Qp v Q₀) (NF.Qp v T₀) hd hd' le_rfl _ hx
  have hcomp := (formF_eq_tc_iff _ _ y).mp hy
  apply h
  refine ⟨(toMat y).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)), ?_⟩
  rw [← Qp_map_eq, ← Qp_map_eq, QuadForm.map_compMat, hcomp]

end Density

/-! ### Representation masses and Siegel's product vanish when there is no representation over $F$ -/

section Vanishing

open QuadFormsKB.Lattices QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-- **If $Q$ does not represent $T$ over $F$, then no lattice does:** $\mathrm{repMass}_T(L) = 0$. -/
theorem repMassT_eq_zero_of_not_rep (Q : QuadForm F N) (L : Lat F N) (T : QuadForm F r)
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) F, Q.compMat X = T) : repMassT Q L T = 0 := by
  unfold repMassT
  have hz : ∀ c ∈ genusClasses Q L, (LatClass.repCountT Q c T : ℝ) / LatClass.autCard Q c = 0 := by
    intro c _
    obtain ⟨M, rfl⟩ := Quotient.exists_rep c
    have h0 : repCountT Q M T = 0 := by
      unfold repCountT
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun X => h ⟨X.1, X.2.2⟩⟩
    show ((repCountT Q M T : ℕ) : ℝ) / _ = 0
    rw [h0, Nat.cast_zero, zero_div]
  exact (finsum_mem_congr rfl hz).trans (finsum_mem_zero _)

/-- **Siegel's product vanishes when $Q_0$ does not represent $T_0$ over $F$:** by the local-global principle
`exists_local_not_rep` some finite prime $v$ has no local representation, so its density
$\alpha_\mathfrak p(Q_0, T_0)$ (`NF.siegelDensity`) vanishes (`localDensityForm_eq_zero_of_not_rep`), hence the infinite product. -/
theorem tprod_siegelDensity_eq_zero_of_not_rep [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N)
    (T₀ : QuadForm (𝓞 F) r) (hrN : r ≤ N)
    (hQ : Lattices.IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hT : Lattices.IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)) :
    ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ T₀ = 0 := by
  obtain ⟨v, hv⟩ := exists_local_not_rep Q₀ T₀ hQ hT h
  have hT0 : T₀.Nondegenerate := nondegenerate_of_map hT.nondegenerate
  have h0 := localDensityForm_eq_zero_of_not_rep v Q₀ T₀ hT0 hrN hv
  exact tprod_of_exists_eq_zero ⟨v, by unfold NF.siegelDensity; rw [h0, mul_zero]⟩

end Vanishing

end QuadFormsKB.Tamagawa.Frames
