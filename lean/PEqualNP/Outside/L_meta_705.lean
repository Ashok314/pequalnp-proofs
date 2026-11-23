import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_705_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

-- The gate restriction argument follows L-meta-562.
private def restrictCircuit {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size)) :
    AndCountCircuit n where
  size := K.card
  leftVars i := C.leftVars (K.orderEmbOfFin rfl i)
  leftGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i))
  rightVars i := C.rightVars (K.orderEmbOfFin rfl i)
  rightGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i))
  outVars := C.outVars
  outGates := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates)

private lemma restrict_mem_leftGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).leftGates i ↔
      K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_rightGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).rightGates i ↔
      K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_outGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (j : Fin K.card) :
    j ∈ (restrictCircuit C K).outGates ↔ K.orderEmbOfFin rfl j ∈ C.outGates := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_wf {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hWF : C.WellFormed) : (restrictCircuit C K).WellFormed := by
  intro i
  constructor
  · intro j hj
    have hj' := (restrict_mem_leftGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).1 _ hj')
  · intro j hj
    have hj' := (restrict_mem_rightGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).2 _ hj')

private lemma restrict_gateVal_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      (restrictCircuit C K).gateVal U i = C.gateVal U (K.orderEmbOfFin rfl i) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [gateVal_unfold (restrictCircuit C K) U i, gateVal_unfold C U (K.orderEmbOfFin rfl i)]
    congr 1
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjF' := (restrict_mem_leftGates C K i j).mp hjF
          refine Or.inr ⟨K.orderEmbOfFin rfl j, hjF', (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ?_⟩
          rwa [← ih j (by omega)]
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := by
            by_contra hnot
            rw [hK j hnot] at hjv
            exact Bool.false_ne_true hjv
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_leftGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjF' := (restrict_mem_rightGates C K i j).mp hjF
          refine Or.inr ⟨K.orderEmbOfFin rfl j, hjF', (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ?_⟩
          rwa [← ih j (by omega)]
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := by
            by_contra hnot
            rw [hK j hnot] at hjv
            exact Bool.false_ne_true hjv
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_rightGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv

private lemma restrict_eval_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false) :
    (restrictCircuit C K).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · have hjO' := (restrict_mem_outGates C K j).mp hjO
      refine Or.inr ⟨K.orderEmbOfFin rfl j, hjO', ?_⟩
      rwa [← restrict_gateVal_eq C K U hK _ j j.isLt]
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · have hjK : j ∈ K := by
        by_contra hnot
        rw [hK j hnot] at hjv
        exact Bool.false_ne_true hjv
      have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hjK
      obtain ⟨j', hj'⟩ := hjr
      refine Or.inr ⟨j', (restrict_mem_outGates C K j').mpr (by rw [hj']; exact hjO), ?_⟩
      rw [restrict_gateVal_eq C K U hK _ j' j'.isLt, hj']
      exact hjv

private def replaceVars {n k : ℕ} (j : Fin k) (A B : Finset (Fin n))
    (F : Finset (Fin k)) : Finset (Fin n) :=
  B ∪ if j ∈ F then A else ∅

private def replaceRefs {k : ℕ} (j : Fin k) (R F : Finset (Fin k)) : Finset (Fin k) :=
  F.erase j ∪ if j ∈ F then R else ∅

-- Replace each read of the erased gate with the variables and reads of its surviving operand.
private abbrev splice {n : ℕ} (C : AndCountCircuit n) (j : Fin C.size)
    (A : Finset (Fin n)) (R : Finset (Fin C.size)) : AndCountCircuit n where
  size := C.size
  leftVars i := if i = j then ∅ else replaceVars j A (C.leftVars i) (C.leftGates i)
  leftGates i := if i = j then ∅ else replaceRefs j R (C.leftGates i)
  rightVars i := replaceVars j A (C.rightVars i) (C.rightGates i)
  rightGates i := replaceRefs j R (C.rightGates i)
  outVars := replaceVars j A C.outVars C.outGates
  outGates := replaceRefs j R C.outGates

private lemma mem_replaceVars {n k : ℕ} (j : Fin k) (A B : Finset (Fin n))
    (F : Finset (Fin k)) (v : Fin n) :
    v ∈ replaceVars j A B F ↔ v ∈ B ∨ (j ∈ F ∧ v ∈ A) := by
  by_cases h : j ∈ F <;> simp [replaceVars, h]

private lemma mem_replaceRefs {k : ℕ} (j : Fin k) (R F : Finset (Fin k)) (l : Fin k) :
    l ∈ replaceRefs j R F ↔ (l ≠ j ∧ l ∈ F) ∨ (j ∈ F ∧ l ∈ R) := by
  by_cases h : j ∈ F
  · simp [replaceRefs, h]
  · simp only [replaceRefs, h, ite_false, Finset.union_empty, Finset.mem_erase, false_and, or_false]

private lemma replaceRefs_lt {k : ℕ} (i j : Fin k) (R F : Finset (Fin k))
    (hR : ∀ l ∈ R, l < j) (hF : ∀ l ∈ F, l < i) :
    ∀ l ∈ replaceRefs j R F, l < i := by
  intro l hl
  rcases (mem_replaceRefs j R F l).1 hl with ⟨_, mem⟩ | ⟨hj, hm⟩
  · exact hF l mem
  · exact (hR l hm).trans (hF j hj)

private lemma splice_wf {n : ℕ} (C : AndCountCircuit n) (j : Fin C.size)
    (A : Finset (Fin n)) (R : Finset (Fin C.size))
    (hwf : C.WellFormed) (hR : ∀ l ∈ R, l < j) : (splice C j A R).WellFormed := by
  intro i
  constructor
  · change ∀ l ∈ (if i = j then ∅ else replaceRefs j R (C.leftGates i)), l < i
    by_cases h : i = j
    · intro l hl
      simp [h] at hl
    · rw [ite_eq_right h]
      exact replaceRefs_lt i j R (C.leftGates i) hR (hwf i).1
  · exact replaceRefs_lt i j R (C.rightGates i) hR (hwf i).2

private def active {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (val : Fin k → Bool) : Prop :=
  (∃ v ∈ B, v ∈ U) ∨ ∃ l ∈ F, val l = true

private lemma sideTrue_active {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (val : Fin k → Bool) (ht : ∀ l ∈ F, l < i) :
    sideTrue U B F i val = true ↔ active U B F val := by
  simp only [sideTrue, decide_eq_true_eq, active]
  constructor
  · rintro (h | ⟨l, hl, _, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨l, hl, hv⟩
  · rintro (h | ⟨l, hl, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨l, hl, ht l hl, hv⟩

private lemma splice_active {n k : ℕ} (j : Fin k) (U A B : Finset (Fin n))
    (R F : Finset (Fin k)) (val val' : Fin k → Bool)
    (hcopy : val j = true ↔ active U A R val)
    (hF : ∀ l ∈ F, l ≠ j → val' l = val l)
    (hR : j ∈ F → ∀ l ∈ R, val' l = val l) :
    active U (replaceVars j A B F) (replaceRefs j R F) val' ↔ active U B F val := by
  constructor
  · rintro (⟨v, hv, hu⟩ | ⟨l, hl, hv⟩)
    · rcases (mem_replaceVars j A B F v).1 hv with hb | ⟨hf, ha⟩
      · exact Or.inl ⟨v, hb, hu⟩
      · exact Or.inr ⟨j, hf, hcopy.2 (Or.inl ⟨v, ha, hu⟩)⟩
    · rcases (mem_replaceRefs j R F l).1 hl with ⟨hne, hm⟩ | ⟨hf, hr⟩
      · exact Or.inr ⟨l, hm, hF l hm hne ▸ hv⟩
      · exact Or.inr ⟨j, hf, hcopy.2 (Or.inr ⟨l, hr, hR hf l hr ▸ hv⟩)⟩
  · rintro (⟨v, hv, hu⟩ | ⟨l, hl, hv⟩)
    · exact Or.inl ⟨v, (mem_replaceVars j A B F v).2 (Or.inl hv), hu⟩
    · by_cases h : l = j
      · subst l
        rcases hcopy.1 hv with ⟨v, ha, hu⟩ | ⟨l, hr, ht⟩
        · exact Or.inl ⟨v, (mem_replaceVars j A B F v).2 (Or.inr ⟨hl, ha⟩), hu⟩
        · exact Or.inr ⟨l, (mem_replaceRefs j R F l).2 (Or.inr ⟨hl, hr⟩), (hR hl l hr).symm ▸ ht⟩
      · exact Or.inr ⟨l, (mem_replaceRefs j R F l).2 (Or.inl ⟨h, hl⟩), (hF l hl h).symm ▸ hv⟩

private lemma splice_gate {n : ℕ} (C : AndCountCircuit n) (j : Fin C.size)
    (U A : Finset (Fin n)) (R : Finset (Fin C.size))
    (hwf : C.WellFormed) (hR : ∀ l ∈ R, l < j)
    (hcopy : C.gateVal U j = true ↔ active U A R (C.gateVal U)) :
    ∀ i : Fin C.size, i ≠ j → (splice C j A R).gateVal U i = C.gateVal U i := by
  let D := splice C j A R
  have step : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → i ≠ j → D.gateVal U i = C.gateVal U i := by
    intro m
    induction m with
    | zero => intro i hi; omega
    | succ m ih =>
      intro i hi hne
      have side (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ l ∈ F, l < i) :
          sideTrue U (replaceVars j A B F) (replaceRefs j R F) i (D.gateVal U) =
            sideTrue U B F i (C.gateVal U) := by
        apply Bool.eq_iff_iff.mpr
        rw [sideTrue_active _ _ _ _ _ (replaceRefs_lt i j R F hR hF),
          sideTrue_active _ _ _ _ _ hF]
        apply splice_active j U A B R F _ _ hcopy
        · intro l hl hn
          have lt := hF l hl
          exact ih l (by omega) hn
        · intro hj l hl
          have lt := (hR l hl).trans (hF j hj)
          exact ih l (by omega) (hR l hl).ne
      rw [gateVal_unfold D U i, gateVal_unfold C U i]
      change (sideTrue U (if i = j then ∅ else replaceVars j A (C.leftVars i) (C.leftGates i))
          (if i = j then ∅ else replaceRefs j R (C.leftGates i)) i (D.gateVal U) &&
        sideTrue U (replaceVars j A (C.rightVars i) (C.rightGates i))
          (replaceRefs j R (C.rightGates i)) i (D.gateVal U)) = _
      rw [ite_eq_right hne, ite_eq_right hne, side _ _ (hwf i).1, side _ _ (hwf i).2]
  intro i hi
  exact step C.size i i.isLt hi

private lemma splice_eval {n : ℕ} (C : AndCountCircuit n) (j : Fin C.size)
    (U A : Finset (Fin n)) (R : Finset (Fin C.size))
    (hwf : C.WellFormed) (hR : ∀ l ∈ R, l < j)
    (hcopy : C.gateVal U j = true ↔ active U A R (C.gateVal U)) :
    (splice C j A R).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  apply decide_eq_decide.mpr
  change active U (replaceVars j A C.outVars C.outGates) (replaceRefs j R C.outGates)
      ((splice C j A R).gateVal U) ↔ active U C.outVars C.outGates (C.gateVal U)
  have eq := splice_gate C j U A R hwf hR hcopy
  exact splice_active j U A C.outVars R C.outGates _ _ hcopy
    (fun l _ hn => eq l hn) (fun _ l hl => eq l (hR l hl).ne)

private abbrev filterInputs {n : ℕ} (C : AndCountCircuit n) (P : Fin n → Prop)
    [DecidablePred P] : AndCountCircuit n :=
  { C with
    leftVars := fun i => (C.leftVars i).filter P
    rightVars := fun i => (C.rightVars i).filter P
    outVars := C.outVars.filter P }

private lemma filter_eval {n : ℕ} (C : AndCountCircuit n) (P : Fin n → Prop)
    [DecidablePred P] (U : Finset (Fin n)) :
    (filterInputs C P).eval U = C.eval (U.filter P) := by
  have side {k : ℕ} (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool) :
      sideTrue U (B.filter P) F i val = sideTrue (U.filter P) B F i val := by
    unfold sideTrue
    apply decide_eq_decide.mpr
    simp only [Finset.mem_filter]
    aesop
  have gates : ∀ d i, (filterInputs C P).gateValFuel U d i = C.gateValFuel (U.filter P) d i := by
    intro d
    induction d with
    | zero => intro i; rfl
    | succ d ih =>
      intro i
      simp only [gateValFuel]
      rw [side, side, show (filterInputs C P).gateValFuel U d = C.gateValFuel (U.filter P) d from funext ih]
  unfold AndCountCircuit.eval
  apply decide_eq_decide.mpr
  change active U (C.outVars.filter P) C.outGates ((filterInputs C P).gateValFuel U C.size) ↔
    active (U.filter P) C.outVars C.outGates (C.gateValFuel (U.filter P) C.size)
  rw [show (filterInputs C P).gateValFuel U C.size = C.gateValFuel (U.filter P) C.size from funext (gates _)]
  simp only [active, Finset.mem_filter]
  aesop

private lemma filter_wf {n : ℕ} (C : AndCountCircuit n) (P : Fin n → Prop)
    [DecidablePred P] (hwf : C.WellFormed) : (filterInputs C P).WellFormed := hwf

private lemma extend_single {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    ∃ I : Finset (Fin n), v ∈ I ∧
      (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧
      (∀ x : Fin n, x ∉ I → ∃ a ∈ I, G.Adj x a) := by
  classical
  let valid (I : Finset (Fin n)) := v ∈ I ∧ ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b
  let choices := Finset.univ.filter valid
  have single : ({v} : Finset (Fin n)) ∈ choices := by
    simp [choices, valid]
  obtain ⟨I, hI, largest⟩ := Finset.exists_max_image choices Finset.card ⟨_, single⟩
  obtain ⟨hv, indep⟩ : valid I := (Finset.mem_filter.mp hI).2
  refine ⟨I, hv, indep, ?_⟩
  intro x hxi
  by_contra! none
  have enlarged : insert x I ∈ choices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_insert_of_mem hv, ?_⟩
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | haI
    · rcases Finset.mem_insert.mp hb with rfl | hbI
      · exact G.irrefl
      · exact none _ hbI
    · rcases Finset.mem_insert.mp hb with rfl | hbI
      · exact fun h => none _ haI h.symm
      · exact indep _ haI _ hbI
  have le := largest (insert x I) enlarged
  rw [Finset.card_insert_of_notMem hxi] at le
  omega

private lemma eval_insert_irrelevant {n : ℕ} (C : AndCountCircuit n) (u : Fin n)
    (out : u ∉ C.outVars)
    (unused : ∀ j : Fin C.size, u ∉ C.leftVars j ∧ u ∉ C.rightVars j)
    (U : Finset (Fin n)) : C.eval (insert u U) = C.eval U := by
  have side (B : Finset (Fin n)) (F : Finset (Fin C.size)) (i : Fin C.size)
      (val : Fin C.size → Bool) (h : u ∉ B) :
      sideTrue (insert u U) B F i val = sideTrue U B F i val := by
    unfold sideTrue
    apply decide_eq_decide.mpr
    simp only [Finset.mem_insert]
    aesop
  have eq : ∀ d i, C.gateValFuel (insert u U) d i = C.gateValFuel U d i := by
    intro d
    induction d with
    | zero => intro i; rfl
    | succ d ih =>
      intro i
      simp only [gateValFuel]
      rw [show C.gateValFuel (insert u U) d = C.gateValFuel U d from funext ih]
      rw [side _ _ _ _ (unused i).1, side _ _ _ _ (unused i).2]
  unfold AndCountCircuit.eval
  apply decide_eq_decide.mpr
  simp only [Finset.mem_insert, gateVal, eq]
  aesop

private lemma isolated_subcube {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n)
    (I : Finset (Fin n)) [DecidableRel G.Adj]
    (ind : ∀ v ∈ I, ∀ w ∈ I,
      ¬ (G.Adj v w ∧ v ≠ u ∧ ¬ G.Adj u v ∧ w ≠ u ∧ ¬ G.Adj u w))
    (dom : ∀ x : Fin n, x ∉ I →
      ∃ v ∈ I, G.Adj x v ∧ x ≠ u ∧ ¬ G.Adj u x ∧ v ≠ u ∧ ¬ G.Adj u v) :
    let J := I.filter (fun v => ¬ G.Adj u v)
    u ∈ J ∧
      (∀ v ∈ J, ∀ w ∈ J, ¬ G.Adj v w) ∧
      (∀ x : Fin n, x ∉ J → ∃ v ∈ J, G.Adj x v) := by
  let J := I.filter (fun v => ¬ G.Adj u v)
  have huI : u ∈ I := by
    by_contra hu
    obtain ⟨v, _, _, bad, _⟩ := dom u hu
    exact bad rfl
  have huJ : u ∈ J := Finset.mem_filter.mpr ⟨huI, G.irrefl⟩
  refine ⟨huJ, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨haI, haU⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbI, hbU⟩ := Finset.mem_filter.mp hb
    by_cases hau : a = u
    · exact hbU (hau ▸ hab)
    by_cases hbu : b = u
    · exact haU (hbu ▸ hab.symm)
    exact ind a haI b hbI ⟨hab, hau, haU, hbu, hbU⟩
  · intro x hx
    by_cases hxI : x ∈ I
    · have adj : G.Adj u x := by
        by_contra h
        exact hx (Finset.mem_filter.mpr ⟨hxI, h⟩)
      exact ⟨u, huJ, adj.symm⟩
    · obtain ⟨v, hvI, adj, _, _, _, hvU⟩ := dom x hxI
      exact ⟨v, Finset.mem_filter.mpr ⟨hvI, hvU⟩, adj⟩

end PEqualNP.Outside.L_meta_705_aux

open PEqualNP.Outside.L_meta_705_aux
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.L_meta_705 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n), (∃ w : Fin n, G.Adj u w) →
    ∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed →
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
        C.eval I = false ∧ ∀ x : Fin n, x ∉ I → C.eval (insert x I) = true) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ I : Finset (Fin n),
          (∀ v ∈ I, ∀ w ∈ I, ¬ (G.Adj v w ∧ v ≠ u ∧ ¬ G.Adj u v ∧ w ≠ u ∧ ¬ G.Adj u w)) →
          (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v ∧ x ≠ u ∧ ¬ G.Adj u x ∧ v ≠ u ∧ ¬ G.Adj u v) →
          C'.eval I = false ∧ ∀ x : Fin n, x ∉ I → C'.eval (insert x I) = true := by
  classical
  intro n G u neighbor C hwf spec
  obtain ⟨w, huw⟩ := neighbor
  have noOut : u ∉ C.outVars := by
    intro out
    obtain ⟨I, hu, ind, dom⟩ := extend_single G u
    have on : C.eval I = true := by
      exact decide_eq_true_eq.mpr (Or.inl ⟨u, out, hu⟩)
    have bad : true = false := on.symm.trans (spec I ind dom).1
    cases bad
  have reads : ∃ j : Fin C.size, u ∈ C.leftVars j ∨ u ∈ C.rightVars j := by
    by_contra! unused
    obtain ⟨I, hw, ind, dom⟩ := extend_single G w
    have hu : u ∉ I := fun hu => ind u hu w hw huw
    have eq := eval_insert_irrelevant C u noOut (by simpa only [not_or] using unused) I
    have result := spec I ind dom
    have bad : true = false := (result.2 u hu).symm.trans (eq.trans result.1)
    cases bad
  obtain ⟨j, hj⟩ := reads
  let A := if u ∈ C.leftVars j then C.rightVars j else C.leftVars j
  let R := if u ∈ C.leftVars j then C.rightGates j else C.leftGates j
  have hR : ∀ l ∈ R, l < j := by
    by_cases hl : u ∈ C.leftVars j
    · simpa [R, hl] using (hwf j).2
    · simpa [R, hl] using (hwf j).1
  have hCopy (U : Finset (Fin n)) (hu : u ∈ U) :
      C.gateVal U j = true ↔ active U A R (C.gateVal U) := by
    rw [gateVal_unfold C U j, Bool.and_eq_true,
      sideTrue_active _ _ _ _ _ (hwf j).1, sideTrue_active _ _ _ _ _ (hwf j).2]
    by_cases hl : u ∈ C.leftVars j
    · have on : active U (C.leftVars j) (C.leftGates j) (C.gateVal U) :=
        Or.inl ⟨u, hl, hu⟩
      simp [A, R, hl, on]
    · have hr := hj.resolve_left hl
      have on : active U (C.rightVars j) (C.rightGates j) (C.gateVal U) :=
        Or.inl ⟨u, hr, hu⟩
      simp [A, R, hl, on]
  let D := splice C j A R
  let K : Finset (Fin D.size) := Finset.univ.erase j
  let P : Fin n → Prop := fun v => ¬ G.Adj u v
  let E := filterInputs (restrictCircuit D K) P
  have hd : D.WellFormed := splice_wf C j A R hwf hR
  have evalEq (U : Finset (Fin n)) (hu : u ∈ U) :
      E.eval U = C.eval (U.filter P) := by
    have hZero (k : Fin D.size) (hk : k ∉ K) : D.gateVal (U.filter P) k = false := by
      have eq : k = j := by
        by_contra h
        exact hk (Finset.mem_erase.mpr ⟨h, Finset.mem_univ k⟩)
      subst k
      rw [gateVal_unfold D (U.filter P) j]
      have leftVars : D.leftVars j = ∅ := by
        change (if j = j then ∅ else replaceVars j A (C.leftVars j) (C.leftGates j)) = ∅
        exact ite_eq_left rfl
      have leftGates : D.leftGates j = ∅ := by
        change (if j = j then ∅ else replaceRefs j R (C.leftGates j)) = ∅
        exact ite_eq_left rfl
      have leftOff : sideTrue (U.filter P) (D.leftVars j) (D.leftGates j) j
          (D.gateVal (U.filter P)) = false := by
        rw [leftVars, leftGates]
        simp [sideTrue]
      simp only [leftOff, Bool.false_and]
    have hu' : u ∈ U.filter P := Finset.mem_filter.mpr ⟨hu, G.irrefl⟩
    exact (filter_eval _ P U).trans
      ((restrict_eval_eq D K (U.filter P) hZero).trans (splice_eval C j _ A R hwf hR (hCopy _ hu')))
  refine ⟨E, filter_wf _ P (restrict_wf D K hd), ?_, ?_⟩
  · change (Finset.univ.erase j).card + 1 ≤ C.size
    rw [Finset.card_erase_add_one (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  · intro I ind dom
    let J := I.filter P
    obtain ⟨hu, hjInd, hjDom⟩ := isolated_subcube G u I ind dom
    have huI := (Finset.mem_filter.mp hu).1
    obtain ⟨hZero, hOne⟩ := spec J hjInd hjDom
    refine ⟨(evalEq I huI).trans hZero, ?_⟩
    intro x hx
    obtain ⟨v, _, _, _, hxU, _⟩ := dom x hx
    have notJ : x ∉ J := fun h => hx (Finset.mem_filter.mp h).1
    have filt : (insert x I).filter P = insert x J := by
      rw [Finset.filter_insert, ite_eq_left (show P x from hxU)]
    rw [evalEq _ (Finset.mem_insert_of_mem huI), filt]
    exact hOne x notJ
