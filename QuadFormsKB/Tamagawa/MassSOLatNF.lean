/-
# The $SO$-mass of an arbitrary lattice in odd rank

**Layer:** a number field $F$ (any class number), $Q_0$ a nondegenerate form over $\mathcal O_F$ of **odd** rank $n$, $L$ an arbitrary
lattice on $V = (F^n, Q_0)$ (`Lat F n`, any Steinitz class).

`mass_SO_eq_two_mul_mass` (the $SO$-mass is twice the $O$-mass) is stated for $L = \mathcal O_F^n$; its only lattice-specific input is
that $O(V)(\mathbb A_f) = SO(V)(\mathbb A_f)\cdot O(\hat L)$, proved there with local reflections of $\mathfrak o_\mathfrak p^n$. In odd rank $-1 \in O(\hat L)$
has determinant $-1$, so the decomposition holds for every lattice (`exists_so_mul_locStab_odd`), and

* **`mass_SO_eq_two_mul_mass_lat`**: $\mathrm{dcMass}(SO(V)(F), SO(\hat L)) = 2\,\mathrm{Mass}(L)$ for every integral $L$ ($n$ odd);
* **`tauSOLat_eq_dcMass`**: $\tau$ computed with $L$ (`LatChange.tauSOLat`) is $\mu_{\mathrm{Tam}}(K_{SO}(L))\cdot\mathrm{dcMass}(SO(V)(F), SO(\hat L))$,
  closing the last gap in odd rank (the case $n = 3$ is needed for $L = \mathcal O^0$).

Source: Conway–Sloane 1988, §2 (proper vs improper classes) [unverified]; Weil 1982, §3.5 [unverified locator].
-/
import QuadFormsKB.Tamagawa.LatticeChangeNF

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain QuadFormsKB.Lattices

section Neg

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- $-1 \in O(V)(R)$. -/
def negOrth (R : Type*) [CommRing R] [Algebra F R] : orthGroup Q R :=
  ⟨-1, mem_orthGroup_of_evalIn Q fun z => by
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec,
      show -z = (-1 : R) • z by simp, evalIn_smul']
    ring⟩

theorem negOrth_val (R : Type*) [CommRing R] [Algebra F R] :
    ((negOrth Q R : orthGroup Q R) : GL (Fin n) R).val = -1 := rfl

theorem det_negOrth (R : Type*) [CommRing R] [Algebra F R] (hn : Odd n) :
    ((negOrth Q R : orthGroup Q R) : GL (Fin n) R).val.det = -1 := by
  rw [negOrth_val, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one, hn.neg_one_pow]

theorem locAct_neg_one (v : HeightOneSpectrum (𝓞 F)) (M : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) :
    locAct v (-1) M = M := by
  ext x
  rw [mem_locAct]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
    exact M.neg_mem hy
  · intro hx
    refine ⟨-x, M.neg_mem hx, ?_⟩
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]

/-- **$O(V)(\mathbb A_f) = SO(V)(\mathbb A_f)\cdot O(\hat L)$ in odd rank**, for every lattice $L$: correct the determinant at each prime by
$-1 \in O(L_\mathfrak p)$. -/
theorem exists_so_mul_locStab_odd (hQ : Q.Nondegenerate) (hn : Odd n) (L : Lat F n) (g : OAf Q) :
    ∃ m ∈ soAf Q, ∃ k ∈ locStab Q L, g = m * k := by
  classical
  let kf : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q (v.adicCompletion F) := fun v =>
    if ((g v : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)).val.det = 1 then 1 else negOrth Q _
  have hkf : ∀ v, kf v ∈ stdStab Q v := by
    intro v; simp only [kf]; split_ifs
    · exact (stdStab Q v).one_mem
    · exact locAct_neg_one v _
  let k : OAf Q := ⟨kf, Filter.Eventually.of_forall hkf⟩
  have hk : k ∈ locStab Q L := by
    intro v
    change locAct v ((kf v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v L.1
    simp only [kf]; split_ifs
    · exact locAct_one _
    · exact locAct_neg_one v _
  refine ⟨g * k⁻¹, fun v => ?_, k, hk, by rw [inv_mul_cancel_right]⟩
  show (((g v * (kf v)⁻¹ : orthGroup Q _)) : GL (Fin n) (v.adicCompletion F)).val.det = 1
  simp only [kf]
  split_ifs with h
  · rw [inv_one, mul_one]; exact h
  · rcases det_eq_one_or_neg_one Q hQ (g v) with h' | h'
    · exact absurd h' h
    · have hi := congrArg Matrix.det
        (Units.inv_mul ((negOrth Q (v.adicCompletion F) : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)))
      rw [det_mul, det_negOrth Q _ hn, det_one] at hi
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, det_mul, h']
      linear_combination hi

end Neg

section MassLat

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The $SO$-mass of any lattice in odd rank is twice its $O$-mass**:
$\mathrm{dcMass}(SO(V)(F), SO(\hat L)) = 2\,\mathrm{Mass}(L)$ for $L$ integral, $Q$ totally positive definite, $n$ odd. -/
@[kb "conwaysloane1988" "§2 (proper vs improper classes) [unverified]"]
theorem mass_SO_eq_two_mul_mass_lat (hQ : Q₀.Nondegenerate) (hn : Odd n) (hpd : IsTotallyPosDef QF)
    (L : Lat F n) (hLi : IsIntegral QF L.1) :
    dcMass ((ratPoints QF).subgroupOf (soAf QF)) ((locStab QF L).subgroupOf (soAf QF)) = 2 * mass QF L := by
  have hn0 : 0 < n := hn.pos
  have hidx := index_soAf_ratPoints Q₀ hQ hn0
  have : ((soAf QF).subgroupOf (ratPoints QF)).FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  have := finite_orbits hpd L hLi
  rw [dcMass_normal (ratPoints QF) (locStab QF L) (soAf QF)
    (exists_so_mul_locStab_odd QF (nondegenerate_map Q₀ hQ) hn L) (finite_stabilizer hpd L hLi), hidx,
    mass_eq_dcMass]
  norm_num

/-- **$\tau$ computed with an arbitrary lattice is the Tamagawa measure times the $SO$-mass** (odd rank):
`tauSOLat Q₀ L` $= \mu_{\mathrm{Tam}}(K_{SO}(L))\cdot\mathrm{dcMass}(SO(V)(F), SO(\hat L))$. -/
theorem tauSOLat_eq_dcMass (hQ : Q₀.Nondegenerate) (hn : Odd n) (hpd : IsTotallyPosDef QF)
    (L : Lat F n) (hLi : IsIntegral QF L.1) :
    LatChange.tauSOLat Q₀ L = LatChange.tamagawaKLat Q₀ L *
      dcMass ((ratPoints QF).subgroupOf (soAf QF)) ((locStab QF L).subgroupOf (soAf QF)) := by
  rw [LatChange.tauSOLat, mass_SO_eq_two_mul_mass_lat Q₀ hQ hn hpd L hLi]

end MassLat

end QuadFormsKB.Tamagawa
