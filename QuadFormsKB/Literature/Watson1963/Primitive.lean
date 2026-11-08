/-
# Watson (1963), §2: Watson-minimal forms are strongly primitive

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), §2, proof of
Theorem 2, p. 551. Watson's lattice $\Lambda_p(f) \subseteq \mathbb Z^n$ (`watsonSub`) is the preimage of the radical
$R_p(f) \subseteq \mathbb F_p^n$ (`radModP`) under reduction mod $p$, so its index in $\mathbb Z^n$ is
$p^{r_p(f)}$ (`index_watsonSub`). Combined with $p^n \le (\det g)^2$ for Watson-minimal forms
(`IsWatsonMinimal.pow_le_det_sq`, $g$ a basis matrix of $\Lambda_p$) this gives (2.7):
$n \le 2 r_p(f)$ (`IsWatsonMinimal.le_two_mul_rankModP`).
-/
import QuadFormsKB.Literature.Watson1963.Rank

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n : ℕ} (p : ℕ) [Fact p.Prime]

/-- Reduction modulo $p$ on vectors, $\mathbb Z^n \to \mathbb F_p^n$ (coordinatewise). -/
def redVec : (Fin n → ℤ) →+ (Fin n → ZMod p) :=
  AddMonoidHom.compLeft (Int.castAddHom (ZMod p)) (Fin n)

theorem redVec_apply (x : Fin n → ℤ) (i : Fin n) : redVec p x i = (x i : ZMod p) := rfl

theorem redVec_surjective : Function.Surjective (redVec (n := n) p) := by
  intro y
  choose x hx using fun i => ZMod.intCast_surjective (y i)
  exact ⟨x, funext fun i => by rw [redVec_apply, hx]⟩

/-- **$\Lambda_p(f)$ is the preimage of $R_p(f)$:** $c \in \Lambda_p(f)$ iff the reduction of $c$ mod $p$ lies in
the radical $R_p(f)$ (`radModP`). Arguments: the prime `p`, the form `Q`, the vector `c`. -/
theorem mem_watsonSub_iff_redVec_mem {Q : QuadForm ℤ n} {c : Fin n → ℤ} :
    c ∈ watsonSub Q (p : ℤ) ↔ redVec p c ∈ radModP p Q := by
  rw [mem_radModP_iff, mem_watsonSub]
  have key : ∀ b : Fin n → ℤ, Q.evalIn (ZMod p) (redVec p c + redVec p b) = Q.evalIn (ZMod p) (redVec p b) ↔
      (p : ℤ) ∣ Q.eval (b + c) - Q.eval b := by
    intro b
    have h1 : redVec p c + redVec p b = redVec p (b + c) := by rw [add_comm, map_add]
    rw [h1]
    have e1' : Q.evalIn (ZMod p) (redVec p (b + c)) = ((Q.eval (b + c) : ℤ) : ZMod p) :=
      evalIn_intCast_vec (S := ZMod p) Q (b + c)
    have e2' : Q.evalIn (ZMod p) (redVec p b) = ((Q.eval b : ℤ) : ZMod p) :=
      evalIn_intCast_vec (S := ZMod p) Q b
    rw [e1', e2', ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h z
    obtain ⟨b, rfl⟩ := redVec_surjective p z
    exact (key b).2 (h b)
  · intro h b
    exact (key b).1 (h _)

/-- **The index of $\Lambda_p$ is $p^{r_p}$** (Watson 1963, §2, proof of Theorem 2, p. 551): the additive subgroup
$\Lambda_p(f) \subseteq \mathbb Z^n$ (`watsonSub`) has index $p^{r_p(f)}$ (`rankModP`). *Proof:* $\Lambda_p(f)$ is the
preimage of $R_p(f)$ under the surjection $\mathbb Z^n \to \mathbb F_p^n$, and $[\mathbb F_p^n : R_p(f)] =
p^{n - \dim R_p(f)}$. Arguments: the prime `p`, the form `Q`. -/
@[kb "watson1963" "§2, proof of Theorem 2, p. 551 (the index of Λ_p is p^{r_p})"]
theorem index_watsonSub (Q : QuadForm ℤ n) :
    (watsonSub Q (p : ℤ)).toAddSubgroup.index = p ^ rankModP p Q := by
  classical
  have hcomap : (watsonSub Q (p : ℤ)).toAddSubgroup =
      (radModP p Q).toAddSubgroup.comap (redVec (n := n) p) := by
    ext c
    exact mem_watsonSub_iff_redVec_mem p
  rw [hcomap, AddSubgroup.index_comap_of_surjective _ (redVec_surjective p)]
  have h := AddSubgroup.card_mul_index (radModP p Q).toAddSubgroup
  have h1 : Nat.card (radModP p Q).toAddSubgroup = p ^ Module.finrank (ZMod p) (radModP p Q) := by
    have := Module.card_eq_pow_finrank (K := ZMod p) (V := radModP p Q)
    rw [Nat.card_eq_fintype_card]; simpa using this
  have h2 : Nat.card (Fin n → ZMod p) = p ^ n := by simp [Nat.card_zmod]
  have hr := rankModP_add_finrank p Q
  rw [h1, h2] at h
  have hp : 0 < p ^ Module.finrank (ZMod p) (radModP p Q) := pow_pos (Fact.out : p.Prime).pos _
  have : p ^ Module.finrank (ZMod p) (radModP p Q) * p ^ rankModP p Q =
      p ^ Module.finrank (ZMod p) (radModP p Q) * (radModP p Q).toAddSubgroup.index := by
    rw [← pow_add, add_comm, hr]
    exact h.symm
  exact (Nat.eq_of_mul_eq_mul_left hp this).symm

/-- **Watson-minimal forms are strongly primitive** (Watson 1963, §2, proof of Theorem 2, p. 551, (2.7)): a
Watson-minimal positive definite form in $n$ variables has $r_p(f) \ge n/2$ for every prime $p$, i.e.
$n \le 2 r_p(f)$. *Proof:* take a basis matrix $B$ of $\Lambda_p$; $|\det B| = [\mathbb Z^n : \Lambda_p] = p^{r_p}$
(`index_watsonSub`), $Q(B\vec x) = p\,Q'(\vec x)$, and minimality gives $p^n \le (\det B)^2 = p^{2 r_p}$
(`IsWatsonMinimal.pow_le_det_sq`). Arguments: `hQ` positive definiteness, `hmin` minimality, the prime `p`. -/
@[kb "watson1963" "§2, proof of Theorem 2, p. 551 ((2.7) for minimal forms)"]
theorem IsWatsonMinimal.le_two_mul_rankModP {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q)
    (hmin : IsWatsonMinimal Q) : n ≤ 2 * rankModP p Q := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set K := watsonSub Q (p : ℤ) with hK
  obtain ⟨B, hB⟩ := wm_exists_matrix_of_submodule hp0 K (smul_mem_watsonSub Q (p : ℤ))
  obtain ⟨X, hBX⟩ := wm_exists_mul_eq (M := B) (N := (p : ℤ) • 1) fun j => by
    rw [smul_mulVec, one_mulVec]; exact (hB _).mp (smul_mem_watsonSub Q (p : ℤ) _)
  have hdetB : B.det ≠ 0 := (wm_det_ne_zero_of_mul_eq hBX hp0).1
  have hrange : Set.range B.mulVec = (K : Set (Fin n → ℤ)) := by
    ext z; exact ((hB z).symm)
  have hinj : Function.Injective (B.mulVecLin) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hdetB hx
  let f : (Fin n → ℤ) →+ K := (B.mulVecLin.toAddMonoidHom).codRestrict K.toAddSubgroup (fun x => (hB _).mpr ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply hinj
      exact congrArg Subtype.val hxy
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := (hB z).mp hz
      exact ⟨x, Subtype.ext hx⟩
  let e : (Fin n → ℤ) ≃+ K := AddEquiv.ofBijective f hf
  have hdet := Submodule.natAbs_det_equiv K e
  have hlin : K.subtype ∘ₗ AddMonoidHom.toIntLinearMap ((e : (Fin n → ℤ) ≃+ K) : (Fin n → ℤ) →+ K) =
      Matrix.toLin' B := by
    ext x : 1
    rfl
  rw [hlin, LinearMap.det_toLin'] at hdet
  have hidx : Nat.card ((Fin n → ℤ) ⧸ K) = p ^ rankModP p Q := by
    rw [← index_watsonSub p Q]; rfl
  rw [hidx] at hdet
  have hdvd : ∀ v, (p : ℤ) ∣ (Q.compMat B).eval v := fun v => by
    rw [QuadForm.eval_compMat]
    exact dvd_eval_of_mem_watsonSub ((hB _).mpr ⟨v, rfl⟩)
  obtain ⟨R, hR⟩ := wm_exists_eq_smul_of_dvd hp0 hdvd
  have hg : ∀ x, Q.eval (B *ᵥ x) = (p : ℤ) * R.eval x := fun x => by
    rw [← QuadForm.eval_compMat, hR, Kneser.eval_smul_form]
  have h := hmin.pow_le_det_sq (Q' := R) hQ hp B hdetB hrange hg
  have hsq : B.det ^ 2 = ((p ^ rankModP p Q : ℕ) : ℤ) ^ 2 := by
    rw [← hdet, ← Int.natAbs_sq]
  rw [hsq] at h
  have h' : p ^ n ≤ (p ^ rankModP p Q) ^ 2 := by exact_mod_cast h
  rw [← pow_mul] at h'
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h'
  omega

end QuadFormsKB.Watson1963
