/-
# Conway–Sloane, Ch. 15, §9: when the genus has more than one spinor genus

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §§9.4–9.6, pp. 390–393
(`conwaysloane1999`).

**Layer.** As in `Section9Kernel.lean`: a regular form `Q : QuadForm ℚ n`, $n \ge 3$, a lattice $L$, a finite set
$P$ of primes with Cassels' condition (3.7) (`hP`), Cassels' group $G = R/ST$ (`CasselsG`) acting simply transitively
on the proper spinor genera of the genus (Cassels Ch. 11, Thm. 3.1, `casselsAct_*`), and Conway–Sloane's spinor
operators $\Delta_p(A)$ (`deltaP`), spinor kernel $Y = X \cap ST$ (Theorem 17, `theorem17`).

**Proves** the converse direction of the one-spinor-genus criterion of `Section9Group.lean`, used for the examples of
§9.6 and §11 and the forms (44):
* `exists_not_sameProperSpinorGenus`: if some $x \in R$ is not in $ST$ (a spinor operator outside the spinor kernel),
  the genus of $L$ contains a lattice $M$ in a different proper spinor genus;
* `not_isometric_of_not_sameProperSpinorGenus`: if moreover $L$ has an improper automorph, no isometry of $V$ maps $L$
  to $M$, so the genus has more than one class;
* `unitPartClass` and `not_mem_casselsST_of_unitPart`: the obstruction used in the book's examples: for a prime
  $q \in P$, the character "square class of the unit part of the $q$-coordinate" kills the generators of Theorem 17
  when (a) every $q$-adically automorphous number has a square unit part, (b) for $p \ne q$ every $p$-adically
  automorphous number $A = p^\alpha a$ has $p^\alpha$ a square in $\mathbb Q_q$, and (c) Cassels' $j$ ($\pm1$) is a
  square in $\mathbb Q_q$; then $\Delta_q(u)$, $u$ a nonsquare unit, is not in the spinor kernel.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Kernel

open NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
  (P : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-! ### A spinor operator outside the kernel gives a second spinor genus -/

/-- **Two spinor genera** (Conway–Sloane §9.4–9.6; Cassels Ch. 11, Thm. 3.1): if some $x \in R$ is not in $ST$
(its spinor operator does not act trivially), then the genus of $L$ contains a lattice $M$ that is not in the
(proper) spinor genus of $L$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.4, p. 390 (a spinor operator outside the kernel moves the spinor genus)"]
theorem exists_not_sameProperSpinorGenus (hn : 3 ≤ n)
    (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {x : CasselsR P} (hx : x ∉ casselsST Q hQ L P) :
    ∃ M : Lat ℚ n, SameGenus Q L.1 M.1 ∧ ¬ SameProperSpinorGenus Q L M := by
  classical
  have hg : (QuotientGroup.mk x : CasselsG Q hQ L P) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨M, hM, hact⟩ := casselsAct_exists Q hQ L P hn hP (QuotientGroup.mk x) (SameGenus.refl Q L.1)
  refine ⟨M, hM, fun hLM => hg ?_⟩
  have h1 : CasselsAct Q hQ L P (QuotientGroup.mk (1 : CasselsR P)) L (latSMul Q 1 L) := by
    refine casselsAct_of_smul Q hQ L P hn hP (SameGenus.refl Q L.1) 1
      (fun v _ => (Tamagawa.soSub Q _).one_mem) (fun _ _ => rfl) 1 fun v => ?_
    rw [show ((1 : OAf Q) v) = 1 from rfl, ← spinorNormHom_apply Q _ hQ, map_one]
    rfl
  have e : latSMul Q (1 : OAf Q) L = L := by
    let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
    exact one_smul (OAf Q) L
  rw [e] at h1
  have h2 : CasselsAct Q hQ L P (QuotientGroup.mk x) L L := by
    obtain ⟨Γ', h1', h2', α, h3, h4, y, h5, h6, h7⟩ := hact
    exact ⟨Γ', h1', h2', α, h3, h4, y, h5, h6, SameProperSpinorGenus.trans Q hLM h7⟩
  have := casselsAct_unique Q hQ L P hn hP (SameGenus.refl Q L.1) h2 h1
  rw [this]
  rfl

include hQ in
/-- **More than one class** (Conway–Sloane §9, "the genus contains more than one class"): if $M$ is not in the proper
spinor genus of $L$ and $L$ has an improper automorph ($\alpha \in O(V)$, $\det\alpha = -1$, $\alpha L = L$), then no
isometry of $V$ maps $L$ onto $M$. -/
theorem not_isometric_of_not_sameProperSpinorGenus {M : Lat ℚ n} (hLM : ¬ SameProperSpinorGenus Q L M)
    {α : orthGroup Q ℚ} (hαdet : ((α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = -1)
    (hαL : glImage (α : GL (Fin n) ℚ) L.1 = L.1) (σ : orthGroup Q ℚ) :
    glImage (σ : GL (Fin n) ℚ) L.1 ≠ M.1 := by
  intro hσ
  have hdet := Tamagawa.det_eq_one_or_neg_one Q hQ σ
  apply hLM
  rcases hdet with h1 | h1
  · exact IsProperIsometric.sameProperSpinorGenus Q ⟨σ, Tamagawa.mem_soSub.mpr h1, hσ⟩
  · refine IsProperIsometric.sameProperSpinorGenus Q ⟨σ * α, Tamagawa.mem_soSub.mpr ?_, ?_⟩
    · rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, h1, hαdet]; norm_num
    · rw [Subgroup.coe_mul, glImage_mul, hαL, hσ]

/-! ### The obstruction used in the book's examples -/

/-- The character of $R$ used for the examples: $r \mapsto$ the square class of $r_q$ modulo the class of $q$ (on
units: the square class of the unit part). -/
def qClassChar (q : P) : CasselsR P →* (SqClass (q.1.adicCompletion ℚ) ⧸
    Subgroup.zpowers (SqClass.mk (primeUnit P q))) :=
  (QuotientGroup.mk' _).comp ((sqClassHom (q.1.adicCompletion ℚ)).comp (Pi.evalMonoidHom _ q))

theorem qClassChar_eq_one_iff (q : P) (r : CasselsR P) :
    qClassChar P q r = 1 ↔ SqClass.mk (r q) ∈ Subgroup.zpowers (SqClass.mk (primeUnit P q)) := by
  simp only [qClassChar, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Pi.evalMonoidHom_apply, sqClassHom_apply]

/-- **A spinor operator outside the kernel** (the argument of Conway–Sloane's examples, §9.6, p. 393: "So $(u_-)_3$
is not in the spinor kernel"): let $q \in P$ and suppose
(a) every $q$-adically automorphous number lies in $\langle q\rangle\mathbb Q_q^{\times2}$;
(b) for $p \ne q$ in $P$ and $A = p^\alpha a$ $p$-adically automorphous, $p^\alpha \in \langle q\rangle
\mathbb Q_q^{\times 2}$ (e.g. $\alpha$ even);
(c) Cassels' $j$ ($-1$ for an indefinite form, $1$ for a definite one) lies in $\langle q\rangle\mathbb Q_q^{\times2}$.
Then a family of units $x$ with $x_q \notin \langle q\rangle\mathbb Q_q^{\times 2}$ (for instance $\Delta_q(u)$, $u$ a
nonsquare unit) is not in $ST$: its spinor operator is not in the spinor kernel. Proof: Theorem 17 (`theorem17`) and
the character `qClassChar`, which kills the generators. -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (an element outside the spinor kernel)"]
theorem not_mem_casselsST_of_qClass (hn : 3 ≤ n) (q : P)
    (ha : ∀ A ∈ localSpinorNormGroup Q hQ q.1 L,
      SqClass.mk A ∈ Subgroup.zpowers (SqClass.mk (primeUnit P q)))
    (hb : ∀ p : P, p ≠ q → ∀ A ∈ localSpinorNormGroup Q hQ p.1 L,
      SqClass.mk (casselsDiag P (natGenUnit p.1 ^ ordP P p A) q) ∈ Subgroup.zpowers (SqClass.mk (primeUnit P q)))
    (hc : SqClass.mk (casselsDiag P (casselsJ Q) q) ∈ Subgroup.zpowers (SqClass.mk (primeUnit P q)))
    {x : CasselsR P} (hxX : x ∈ casselsX P)
    (hxq : SqClass.mk (x q) ∉ Subgroup.zpowers (SqClass.mk (primeUnit P q))) :
    x ∉ casselsST Q hQ L P := by
  classical
  intro hxST
  have hY : x ∈ casselsY Q hQ L P := ⟨hxX, hxST⟩
  rw [theorem17 Q hQ L P hn] at hY
  have hle : Subgroup.closure (thm17Gens Q hQ L P) ≤ (qClassChar P q).ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (⟨p, A, hA, rfl⟩ | hg)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, qClassChar_eq_one_iff]
      by_cases hpq : p = q
      · subst hpq
        rw [deltaP_apply_self, SqClass.mk_mul,
          show SqClass.mk (primeUnit P p ^ (-ordP P p A)) = SqClass.mk (primeUnit P p) ^ (-ordP P p A) from
            map_zpow (sqClassHom _) _ _]
        exact Subgroup.mul_mem _ (ha A hA) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
      · rw [deltaP_apply_ne P (Ne.symm hpq)]
        exact hb p hpq A hA
    · rw [Set.mem_singleton_iff] at hg
      rw [hg, SetLike.mem_coe, MonoidHom.mem_ker, qClassChar_eq_one_iff]
      exact hc
  have := hle hY
  rw [MonoidHom.mem_ker, qClassChar_eq_one_iff] at this
  exact hxq this

/-- **A spinor operator outside the kernel, general form**: as `not_mem_casselsST_of_qClass` with
$\langle q\rangle\mathbb Q_q^{\times 2}$ replaced by any subgroup $H$ of square classes of $\mathbb Q_q$ containing the
class of $q$ (used when Cassels' $j = -1$ must be allowed, as for the indefinite forms of §11). -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (an element outside the spinor kernel)"]
theorem not_mem_casselsST_of_subgroup (hn : 3 ≤ n) (q : P) (H : Subgroup (SqClass (q.1.adicCompletion ℚ)))
    (hH : SqClass.mk (primeUnit P q) ∈ H)
    (ha : ∀ A ∈ localSpinorNormGroup Q hQ q.1 L, SqClass.mk A ∈ H)
    (hb : ∀ p : P, p ≠ q → ∀ A ∈ localSpinorNormGroup Q hQ p.1 L,
      SqClass.mk (casselsDiag P (natGenUnit p.1 ^ ordP P p A) q) ∈ H)
    (hc : SqClass.mk (casselsDiag P (casselsJ Q) q) ∈ H)
    {x : CasselsR P} (hxX : x ∈ casselsX P) (hxq : SqClass.mk (x q) ∉ H) :
    x ∉ casselsST Q hQ L P := by
  classical
  intro hxST
  have hY : x ∈ casselsY Q hQ L P := ⟨hxX, hxST⟩
  rw [theorem17 Q hQ L P hn] at hY
  let χ : CasselsR P →* SqClass (q.1.adicCompletion ℚ) ⧸ H :=
    (QuotientGroup.mk' H).comp ((sqClassHom (q.1.adicCompletion ℚ)).comp (Pi.evalMonoidHom _ q))
  have hχ : ∀ r : CasselsR P, χ r = 1 ↔ SqClass.mk (r q) ∈ H := fun r => by
    simp only [χ, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Pi.evalMonoidHom_apply, sqClassHom_apply]
  have hle : Subgroup.closure (thm17Gens Q hQ L P) ≤ χ.ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (⟨p, A, hA, rfl⟩ | hg)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, hχ]
      by_cases hpq : p = q
      · subst hpq
        rw [deltaP_apply_self, SqClass.mk_mul,
          show SqClass.mk (primeUnit P p ^ (-ordP P p A)) = SqClass.mk (primeUnit P p) ^ (-ordP P p A) from
            map_zpow (sqClassHom _) _ _]
        exact H.mul_mem (ha A hA) (H.zpow_mem hH _)
      · rw [deltaP_apply_ne P (Ne.symm hpq)]
        exact hb p hpq A hA
    · rw [Set.mem_singleton_iff] at hg
      rw [hg, SetLike.mem_coe, MonoidHom.mem_ker, hχ]
      exact hc
  have := hle hY
  rw [MonoidHom.mem_ker, hχ] at this
  exact hxq this

end QuadFormsKB.ConwaySloane
