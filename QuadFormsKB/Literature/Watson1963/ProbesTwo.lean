/-
# Watson (1963), Lemma 2 at $p = 2$: the named input `WatsonLocalProbesTwo` is proved

The case analysis described in `Probes2.lean`: `localProbes_two` and `watsonLocalProbesTwo_holds`.
-/
import QuadFormsKB.Literature.Watson1963.Probes2

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

theorem map_diag_one (c : ℤ) :
    (QuadForm.diag ![c]).map (Int.castRingHom ℤ_[2]) = QuadForm.diag ![(c : ℤ_[2])] := by
  rw [map_diag]; congr 1; ext i; fin_cases i; rfl

theorem map_diag_two (a c : ℤ) :
    (QuadForm.diag ![a, c]).map (Int.castRingHom ℤ_[2]) = QuadForm.diag ![(a : ℤ_[2]), (c : ℤ_[2])] := by
  rw [map_diag]; congr 1; ext i; fin_cases i <;> rfl

theorem isUnit_of_not_two_dvd {x : ℤ_[2]} (h : ¬ (2 : ℤ_[2]) ∣ x) : IsUnit x :=
  isUnit_of_toZMod_ne_zero (toZMod_ne_zero_of_not_dvd h)

/-- **Watson 1963, Lemma 2 at $p = 2$, for the probes of §8** (see `Probes2.lean`): a Watson-minimal positive
definite form $f$ in $n \ge 12$ variables represents over $\mathbb Z_2$ the forms $A_5, \Phi_5$ if $r_2(f) \ge 6$;
$A_6, \Phi_6$ if $r_2(f) \ge 7$; $E_7$ if $r_2(f) \ge 8$; $E_8$ if $r_2(f) \ge 9$; $\Phi_9$ if $r_2(f) \ge 10$.
Arguments: `hf` positive definiteness, `hmin` minimality, `hn : 12 ≤ n`. -/
@[kb "watson1963" "§4, Lemma 2, (4.12), (4.15)–(4.16), pp. 555–556 (local representations at p = 2)"]
theorem localProbes_two {n : ℕ} {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (hn : 12 ≤ n) :
    (6 ≤ rankModP 2 f → RepOver ℤ_[2] f (phiA 5) ∧ RepOver ℤ_[2] f (phiD 4)) ∧
    (7 ≤ rankModP 2 f → RepOver ℤ_[2] f (phiA 6) ∧ RepOver ℤ_[2] f (phiD 5)) ∧
    (8 ≤ rankModP 2 f → RepOver ℤ_[2] f formE7) ∧
    (9 ≤ rankModP 2 f → RepOver ℤ_[2] f formE8) ∧
    (10 ≤ rankModP 2 f → RepOver ℤ_[2] f (phiD 8)) := by
  classical
  obtain ⟨k, m, hm, H, K, hH, horth, hspan, huniq, hpsi, h2k, hr1, hrev⟩ := exists_decomp_two f
  set F := f.map (Int.castRingHom ℤ_[2]) with hF
  set U := F.compMat H with hUdef
  set ψ := F.compMat K with hψdef
  have hU : IsUnit U.hessian.det := by rw [hUdef, QuadForm.hessian_compMat]; exact hH
  have hSF : SqFreePsi ψ :=
    sqFreePsi_of_decomp F (IsWatsonMinimal.sqFree2 hf hmin) H K hH horth hspan huniq hpsi
  have hψ : ∀ c, F.eval (K *ᵥ c) = ψ.eval c := fun c => (QuadForm.eval_compMat F K c).symm
  have hodd : rankModP 2 f = 2 * k + 1 → ∃ c₀, ¬ (2 : ℤ_[2]) ∣ ψ.eval c₀ := by
    intro hr
    by_contra hcon
    push Not at hcon
    have := hrev (fun c => by rw [hψ]; exact hcon c)
    omega
  have hYpart : ∀ {v : ℕ} (Y : QuadForm ℤ v), ¬ (2 : ℤ) ∣ Y.hessian.det → Even v → v + 2 ≤ 2 * k →
      ∃ (M₁ : Matrix (Fin n) (Fin v) ℤ_[2]) (l : ℕ) (M' : Matrix (Fin n) (Fin l) ℤ_[2]),
        v + l = 2 * k ∧ (∀ y, F.eval (M₁ *ᵥ y) = (Y.map (Int.castRingHom ℤ_[2])).eval y) ∧
        (∀ y c, (M₁ *ᵥ y) ⬝ᵥ (F.hessian *ᵥ (M' *ᵥ c)) = 0) ∧ IsUnit (F.compMat M').hessian.det ∧
        (∀ y c, (M₁ *ᵥ y) ⬝ᵥ (F.hessian *ᵥ (K *ᵥ c)) = 0) ∧
        (∀ y c, (M' *ᵥ y) ⬝ᵥ (F.hessian *ᵥ (K *ᵥ c)) = 0) := by
    intro v Y hY hv hle
    obtain ⟨H₁, l, K₁, hl, hH₁, horth₁, hK₁⟩ :=
      exists_unimod_complement U (Y.map (Int.castRingHom ℤ_[2])) hU (isUnit_map_det Y hY) ⟨k, by ring⟩ hv hle
    refine ⟨H * H₁, l, H * K₁, hl, fun y => ?_, fun y c => ?_, ?_, fun y c => ?_, fun y c => ?_⟩
    · rw [← mulVec_mulVec, ← hH₁, hUdef, QuadForm.eval_compMat]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, dot_compMat]; exact horth₁ y c
    · rw [← QuadForm.compMat_mul]; exact hK₁
    · rw [← mulVec_mulVec]; exact horth _ c
    · rw [← mulVec_mulVec]; exact horth _ c
  -- unit summands
  have hUnitS : ∀ {v : ℕ} (Y : QuadForm ℤ v), ¬ (2 : ℤ) ∣ Y.hessian.det → Even v → v + 2 ≤ 2 * k →
      ∀ c : ℤ, Odd c →
        Rep2 F (QuadForm.orthSum (Y.map (Int.castRingHom ℤ_[2])) (QuadForm.diag ![(c : ℤ_[2])])) := by
    intro v Y hY hv hle c hc
    obtain ⟨M₁, l, M', hl, h₁, ho, hM', -, -⟩ := hYpart Y hY hv hle
    obtain ⟨r, hr⟩ := hv
    obtain ⟨x, hx⟩ := exists_eval_eq_unit' (F.compMat M') hM' ⟨k - r, by omega⟩ (by omega) (isUnit_of_odd hc)
    exact rep2_orthSum_diag_one M₁ h₁ (M' *ᵥ x) (by rw [← QuadForm.eval_compMat]; exact hx) (fun y => ho y x)
  -- summands 2u
  have hTwoS : ∀ {v : ℕ} (Y : QuadForm ℤ v), ¬ (2 : ℤ) ∣ Y.hessian.det → Even v → v + 2 ≤ 2 * k → v ≤ 8 →
      ∀ u : ℤ, Odd u →
        Rep2 F (QuadForm.orthSum (Y.map (Int.castRingHom ℤ_[2])) (QuadForm.diag ![((2 * u : ℤ) : ℤ_[2])])) := by
    intro v Y hY hv hle hv8 u hu
    obtain ⟨M₁, l, M', hl, h₁, ho, hM', h₁K, hM'K⟩ := hYpart Y hY hv hle
    obtain ⟨r, hr⟩ := hv
    have hE : Even l := ⟨k - r, by omega⟩
    by_cases hl4 : 4 ≤ l
    · obtain ⟨x, -, hx, -, -⟩ := exists_orth_pair' (F.compMat M') hM' hE hl4 ((2 * u : ℤ) : ℤ_[2]) isUnit_one
      exact rep2_orthSum_diag_one M₁ h₁ (M' *ᵥ x) (by rw [← QuadForm.eval_compMat]; exact hx) (fun y => ho y x)
    by_cases hev : ∀ c, (2 : ℤ_[2]) ∣ ψ.eval c
    · obtain ⟨c, hc⟩ := psi_represents_two_mul_unit ψ hpsi hSF hev (by omega) (isUnit_of_odd hu)
      exact rep2_orthSum_diag_one M₁ h₁ (K *ᵥ c) (by rw [hψ, hc]; push_cast; ring) (fun y => h₁K y c)
    · push Not at hev
      obtain ⟨c₀, hc₀⟩ := hev
      have hw : IsUnit (((2 * u : ℤ) : ℤ_[2]) - ψ.eval c₀) := by
        refine isUnit_of_not_two_dvd fun h => hc₀ ?_
        have : (2 : ℤ_[2]) ∣ ((2 * u : ℤ) : ℤ_[2]) := ⟨(u : ℤ_[2]), by push_cast; ring⟩
        exact (dvd_sub_right this).1 h
      obtain ⟨x', hx'⟩ := exists_eval_eq_unit' (F.compMat M') hM' hE (by omega) hw
      refine rep2_orthSum_diag_one M₁ h₁ (M' *ᵥ x' + K *ᵥ c₀) ?_ (fun y => ?_)
      · have hp := QuadForm.eval_polar F (M' *ᵥ x') (K *ᵥ c₀)
        rw [hM'K, ← QuadForm.eval_compMat, hx', hψ] at hp
        linear_combination hp
      · rw [mulVec_add, dotProduct_add, ho, h₁K, add_zero]
  -- unimodular probes
  have hUni : ∀ {v : ℕ} (Y : QuadForm ℤ v), ¬ (2 : ℤ) ∣ Y.hessian.det → Even v → 2 ≤ v → v ≤ 2 * k →
      (v = 2 * k → rankModP 2 f = 2 * k + 1) → RepOver ℤ_[2] f Y := by
    intro v Y hY hv hv2 hle htight
    refine repOver_of_rep2 ?_
    by_cases hle2 : v + 2 ≤ 2 * k
    · obtain ⟨H₁, hH₁⟩ := exists_rep_unimod' U (Y.map (Int.castRingHom ℤ_[2])) hU (isUnit_map_det Y hY)
        ⟨k, by ring⟩ hv hle2
      exact ⟨H * H₁, fun y => by rw [← mulVec_mulVec, ← hH₁, hUdef, QuadForm.eval_compMat]⟩
    · obtain ⟨r, hr⟩ := hv
      have hvk : v = 2 * k := by omega
      obtain ⟨c₀, hc₀⟩ := hodd (htight hvk)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      subst hvk
      exact rep2_unimodular_of_odd_vec F H hH (K *ᵥ c₀) (by rw [hψ]; exact hc₀) (fun y => horth y c₀)
        (Y.map (Int.castRingHom ℤ_[2])) (isUnit_map_det Y hY)
  have hA4 := not_two_dvd_phiA_det 4 (by decide)
  refine ⟨fun hr => ⟨?_, ?_⟩, fun hr => ⟨?_, ?_⟩, fun hr => ?_, fun hr => ?_, fun hr => ?_⟩
  · -- A₅ = A₄ ⊥ ⟨c⟩
    obtain ⟨T, c, hT, hc, hdec⟩ := phiA5_decomp
    refine repOver_of_decomp T hT hdec (rep2_map_orthSum ?_)
    rw [map_diag_one]
    exact hUnitS (phiA 4) hA4 (by decide) (by omega) c hc
  · -- D₅ = A₄ ⊥ ⟨2u⟩
    obtain ⟨T, u, hT, hu, hdec⟩ := phiD4_decomp
    refine repOver_of_decomp T hT hdec (rep2_map_orthSum ?_)
    rw [map_diag_one]
    exact hTwoS (phiA 4) hA4 (by decide) (by omega) (by norm_num) u hu
  · -- A₆ unimodular
    exact hUni (phiA 6) (not_two_dvd_phiA_det 6 (by decide)) (by decide) (by norm_num) (by omega)
      (fun _ => by omega)
  · -- D₆ = A₄ ⊥ ⟨a, c⟩
    obtain ⟨M₁, l, M', hl, h₁, ho, hM', h₁K, hM'K⟩ := hYpart (phiA 4) hA4 (by decide) (by omega)
    have hE : Even l := ⟨k - 2, by omega⟩
    by_cases hl4 : 4 ≤ l
    · obtain ⟨T, a, c, hT, -, hc, hdec⟩ := phiD5_decomp3
      refine repOver_of_decomp T hT hdec (rep2_map_orthSum ?_)
      rw [map_diag_two]
      obtain ⟨x, y, hx, hy, hxy⟩ := exists_orth_pair' (F.compMat M') hM' hE hl4 (a : ℤ_[2]) (isUnit_of_odd hc)
      exact rep2_orthSum_diag_two M₁ h₁ (M' *ᵥ x) (M' *ᵥ y) (by rw [← QuadForm.eval_compMat]; exact hx)
        (by rw [← QuadForm.eval_compMat]; exact hy) (by rw [dot_compMat]; exact hxy) (fun z => ho z x)
        (fun z => ho z y)
    · obtain ⟨c₀, hc₀⟩ := hodd (by omega)
      obtain ⟨c₁, hc₁⟩ := psi_exists_three_mod_four ψ hpsi hSF c₀ hc₀ (by omega)
      obtain ⟨e, he⟩ := hc₁
      have ht : IsUnit (ψ.eval c₁) := by
        refine isUnit_of_not_two_dvd fun h => ?_
        apply not_two_dvd_one'
        have : (1 : ℤ_[2]) = ψ.eval c₁ - 2 * (2 * e + 1) := by linear_combination -he
        rw [this]; exact dvd_sub h (dvd_mul_right 2 _)
      have hfin : ∀ (T : Matrix (Fin 6) (Fin 6) ℤ) (a c : ℤ), Odd T.det → Odd c →
          (phiD 5).compMat T = QuadForm.orthSum (phiA 4) (QuadForm.diag ![a, c]) →
          (8 : ℤ_[2]) ∣ ψ.eval c₁ - a → RepOver ℤ_[2] f (phiD 5) := by
        intro T a c hT hc hdec h8
        have ha : IsUnit ((a : ℤ) : ℤ_[2]) := by
          refine isUnit_of_not_two_dvd fun h => ?_
          apply (isUnit_iff_not_dvd 2 (ψ.eval c₁)).1 ht
          obtain ⟨q, hq⟩ := h8
          obtain ⟨q', hq'⟩ := h
          exact ⟨4 * q + q', by push_cast; linear_combination hq + hq'⟩
        obtain ⟨s, hs⟩ := exists_sq_mul_eq ht ha h8
        obtain ⟨y', hy'⟩ := exists_eval_eq_unit' (F.compMat M') hM' hE (by omega) (isUnit_of_odd hc)
        refine repOver_of_decomp T hT hdec (rep2_map_orthSum ?_)
        rw [map_diag_two]
        refine rep2_orthSum_diag_two M₁ h₁ (K *ᵥ (s • c₁)) (M' *ᵥ y') ?_
          (by rw [← QuadForm.eval_compMat]; exact hy') ?_ (fun z => h₁K z _) (fun z => ho z y')
        · rw [hψ, eval_smul_sq, hs]
        · rw [dot_symm, hM'K]
      by_cases he2 : (2 : ℤ_[2]) ∣ e
      · obtain ⟨T, a, c, hT, ha8, hc, hdec⟩ := phiD5_decomp3
        refine hfin T a c hT hc hdec ?_
        obtain ⟨e', he'⟩ := he2
        obtain ⟨q, hq⟩ := intCast_dvd_eight_of_emod ha8
        exact ⟨e' - q, by push_cast at hq; linear_combination he + 4 * he' - hq⟩
      · obtain ⟨T, a, c, hT, ha8, hc, hdec⟩ := phiD5_decomp7
        refine hfin T a c hT hc hdec ?_
        obtain ⟨e', he'⟩ := odd_eq_one_add he2
        obtain ⟨q, hq⟩ := intCast_dvd_eight_of_emod ha8
        exact ⟨e' - q, by push_cast at hq; linear_combination he + 4 * he' - hq⟩
  · -- E₇ = A₆ ⊥ ⟨c⟩
    obtain ⟨T, c, hT, hc, hdec⟩ := formE7_decomp
    refine repOver_of_decomp T hT hdec (rep2_map_orthSum ?_)
    rw [map_diag_one]
    exact hUnitS (phiA 6) (not_two_dvd_phiA_det 6 (by decide)) (by decide) (by omega) c hc
  · -- E₈ unimodular
    exact hUni formE8 (by rw [formE8_hessian_det]; decide) (by decide) (by norm_num) (by omega) (fun _ => by omega)
  · -- D₉ = A₈ ⊥ ⟨2u⟩
    obtain ⟨T, u, hT, hu, hdec⟩ := phiD8_decomp
    refine repOver_of_decomp T hT hdec (rep2_map_orthSum ?_)
    rw [map_diag_one]
    exact hTwoS (phiA 8) (not_two_dvd_phiA_det 8 (by decide)) (by decide) (by omega) (by norm_num) u hu

/-- **The named input `WatsonLocalProbesTwo` holds** (`localProbes_two`). -/
@[kb "watson1963" "§4, Lemma 2 at p = 2 (proof of WatsonLocalProbesTwo)"]
theorem watsonLocalProbesTwo_holds : WatsonLocalProbesTwo :=
  ⟨fun _ _ hf hmin hn => localProbes_two hf hmin hn⟩

end QuadFormsKB.Watson1963
