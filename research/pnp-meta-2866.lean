import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Induction
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2866

variable {α : Type*} [DecidableEq α]

private def ConstantOn (labels : α → α) (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, labels x = labels y

omit [DecidableEq α] in
private theorem constantOnSmall (labels : α → α) {S : Finset α} (h : S.card ≤ 1) :
    ConstantOn labels S := by
  intro x hx y hy
  exact congrArg labels (Finset.card_le_one.mp h x hx y hy)

private theorem labelUnion (labels : α → α) (T A B : Finset α)
    (hA : ConstantOn labels A) (hB : ConstantOn labels B) :
    ∃ relabel : α → α, ConstantOn (relabel ∘ labels) (A ∪ B) ∧
      (T.image labels).card ≤ (T.image (relabel ∘ labels)).card + 1 := by
  classical
  by_cases Aempty : A = ∅
  · subst A
    exact ⟨id, by simpa using hB, by simp⟩
  by_cases Bempty : B = ∅
  · subst B
    exact ⟨id, by simpa using hA, by simp⟩
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr Aempty
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr Bempty
  let relabel := fun t => if t = labels b then labels a else t
  have same (x : α) (hx : x ∈ A ∪ B) : relabel (labels x) = labels a := by
    rcases Finset.mem_union.mp hx with hxA | hxB
    · rw [hA x hxA a ha]
      simp [relabel]
    · rw [hB x hxB b hb]
      simp [relabel]
  refine ⟨relabel, fun x hx y hy => (same x hx).trans (same y hy).symm, ?_⟩
  have hsub : T.image labels ⊆ insert (labels b) (T.image (relabel ∘ labels)) := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    by_cases hxb : labels x = labels b
    · exact Finset.mem_insert.mpr (Or.inl hxb)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, by simp [relabel, hxb]⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

private def BinaryUnions (xs : List (Finset α)) : Prop :=
  ∀ j S, xs[j]? = some S → ∃ A B : Finset α, S = A ∪ B ∧
    (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j)

private def paid (T S : Finset α) : Bool := decide (1 < S.card ∧ S ⊆ T)

private theorem processLabels (T : Finset α) (xs : List (Finset α)) (hxs : BinaryUnions xs) :
    ∃ labels : α → α, (∀ S ∈ xs, S ⊆ T → ConstantOn labels S) ∧
      T.card ≤ (T.image labels).card + xs.countP (paid T) := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨id, by simp, by simp⟩
  | append_singleton xs S ih =>
    have hprefix : BinaryUnions xs := by
      intro j U hU
      have hj : j < xs.length := List.getElem?_eq_some_iff.mp hU |>.choose
      have hfull : (xs ++ [S])[j]? = some U := by
        rw [List.getElem?_append_left hj, hU]
      obtain ⟨A, B, hEq, hA, hB⟩ := hxs j U hfull
      have htake : (xs ++ [S]).take j = xs.take j := List.take_append_of_le_length hj.le
      exact ⟨A, B, hEq, by simpa only [htake] using hA, by simpa only [htake] using hB⟩
    obtain ⟨labels, hconstant, hbound⟩ := ih hprefix
    by_cases hcost : 1 < S.card ∧ S ⊆ T
    · have hlast : (xs ++ [S])[xs.length]? = some S := by simp
      obtain ⟨A, B, he, hA, hB⟩ := hxs xs.length S hlast
      have htake : (xs ++ [S]).take xs.length = xs := by
        rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have hsub : A ∪ B ⊆ T := he ▸ hcost.2
      have hAconstant : ConstantOn labels A := by
        rcases hA with ha | ha
        · exact constantOnSmall labels ha
        · rw [htake] at ha
          exact hconstant A ha (Finset.subset_union_left.trans hsub)
      have hBconstant : ConstantOn labels B := by
        rcases hB with hb | hb
        · exact constantOnSmall labels hb
        · rw [htake] at hb
          exact hconstant B hb (Finset.subset_union_right.trans hsub)
      obtain ⟨relabel, hmerged, hdropped⟩ := labelUnion labels T A B hAconstant hBconstant
      refine ⟨relabel ∘ labels, ?_, ?_⟩
      · intro U hU hsub x hx y hy
        rcases List.mem_append.mp hU with hprevious | hlast
        · exact congrArg relabel (hconstant U hprevious hsub x hx y hy)
        · have hu : U = S := List.mem_singleton.mp hlast
          subst U
          rw [he] at hx hy
          exact hmerged x hx y hy
      · have hstep : (xs ++ [S]).countP (paid T) = xs.countP (paid T) + 1 := by
          simp [paid, hcost]
        rw [hstep]
        omega
    · refine ⟨labels, ?_, ?_⟩
      · intro U hU hsub
        rcases List.mem_append.mp hU with hprevious | hlast
        · exact hconstant U hprevious hsub
        · have hu : U = S := List.mem_singleton.mp hlast
          subst U
          exact constantOnSmall labels (Nat.le_of_not_gt fun h => hcost ⟨h, hsub⟩)
      · exact hbound.trans (Nat.add_le_add_left (by simp) _)

theorem singleOutputUnionBound (N : ℕ) (xs : List (Finset (Fin N)))
    (hxs : ∀ j S, xs[j]? = some S → ∃ A B : Finset (Fin N), S = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j)) :
    ∀ T ∈ xs, T.card ≤ Fintype.card {j : Fin xs.length //
      1 < (xs.get j).card ∧ xs.get j ⊆ T} + 1 := by
  intro T hT
  obtain ⟨labels, hconstant, hbound⟩ := processLabels T xs hxs
  have hlabels : (T.image labels).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hconstant T hT (Finset.Subset.refl T) a ha b hb
  have hcount : xs.countP (paid T) = Fintype.card {j : Fin xs.length //
      1 < (xs.get j).card ∧ xs.get j ⊆ T} := by
    conv_lhs => rw [← List.ofFn_get xs]
    rw [List.countP_ofFn, Fintype.card_subtype]
    simp only [paid, decide_eq_true_eq]
  omega

open scoped BigOperators

theorem sharedIncidenceUnionBound {q N : ℕ} (line : Fin N → Finset (Fin N))
    (hdegree : ∀ l, (line l).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ line l ∧ p' ∈ line l)
    (xs : List (Finset (Fin N)))
    (hxs : ∀ j S, xs[j]? = some S → ∃ A B : Finset (Fin N), S = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j))
    (houtputs : ∀ l, line l ∈ xs) : N * q ≤ xs.length := by
  let charged (l : Fin N) : Finset (Fin xs.length) := Finset.univ.filter fun j =>
    1 < (xs.get j).card ∧ xs.get j ⊆ line l
  have hline (l : Fin N) : q ≤ (charged l).card := by
    have h := singleOutputUnionBound N xs hxs (line l) (houtputs l)
    rw [Fintype.card_subtype] at h
    change (line l).card ≤ (charged l).card + 1 at h
    rw [hdegree] at h
    omega
  have hdisjoint : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint charged := by
    intro l _ l' _ hne
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨hlarge, hsub⟩ := (Finset.mem_filter.mp hj).2
    have hsub' := (Finset.mem_filter.mp hj').2.2
    obtain ⟨p, p', hp, hp', hdiff⟩ := Finset.one_lt_card_iff.mp hlarge
    exact hne ((hunique p p' hdiff).unique ⟨hsub hp, hsub hp'⟩ ⟨hsub' hp, hsub' hp'⟩)
  calc
    N * q = ∑ _l : Fin N, q := by simp
    _ ≤ ∑ l : Fin N, (charged l).card := Finset.sum_le_sum fun l _ => hline l
    _ = (Finset.univ.biUnion charged).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ xs.length := (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

private theorem binaryUnionsAppend {xs ys : List (Finset α)} (hxs : BinaryUnions xs)
    (hys : BinaryUnions ys) : BinaryUnions (xs ++ ys) := by
  intro j S hS
  by_cases hj : j < xs.length
  · rw [List.getElem?_append_left hj] at hS
    simpa only [List.take_append_of_le_length hj.le] using hxs j S hS
  · have hj' : xs.length ≤ j := by omega
    rw [List.getElem?_append_right hj'] at hS
    obtain ⟨A, B, hEq, hA, hB⟩ := hys (j - xs.length) S hS
    have hincl {U : Finset α} (hU : U ∈ ys.take (j - xs.length)) :
        U ∈ (xs ++ ys).take j := by
      rw [List.take_append, List.take_of_length_le hj']
      exact List.mem_append_right _ hU
    exact ⟨A, B, hEq, hA.imp_right hincl, hB.imp_right hincl⟩

private def buildRow : List α → List (Finset α)
  | [] => []
  | a :: rest => if rest.isEmpty then [] else buildRow rest ++ [(a :: rest).toFinset]

private theorem buildRowLength (row : List α) : (buildRow row).length = row.length - 1 := by
  induction row with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b tail =>
      simp only [buildRow, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.length_append, List.length_cons, List.length_nil] at ih ⊢
      omega

private theorem buildRowOutput (row : List α) (hrow : 2 ≤ row.length) :
    row.toFinset ∈ buildRow row := by
  cases row with
  | nil => simp at hrow
  | cons a rest =>
    cases rest with
    | nil => simp at hrow
    | cons b tail => simp [buildRow]

private theorem buildRowBinary (row : List α) : BinaryUnions (buildRow row) := by
  induction row with
  | nil => simp [BinaryUnions, buildRow]
  | cons a rest ih =>
    cases rest with
    | nil => simp [BinaryUnions, buildRow]
    | cons b tail =>
      let rest := b :: tail
      let done := buildRow rest
      change BinaryUnions (done ++ [(a :: rest).toFinset])
      intro j S hS
      by_cases hj : j < done.length
      · rw [List.getElem?_append_left hj] at hS
        simpa only [List.take_append_of_le_length hj.le] using ih j S hS
      · have hj' : j = done.length := by
          have hb := (List.getElem?_eq_some_iff.mp hS).choose
          simp only [List.length_append, List.length_singleton] at hb
          omega
        subst j
        have hS' : (a :: rest).toFinset = S := by simpa using hS
        refine ⟨{a}, rest.toFinset, ?_, Or.inl (by simp), ?_⟩
        · rw [← hS', List.toFinset_cons, Finset.singleton_union]
        · by_cases hrest : 2 ≤ rest.length
          · apply Or.inr
            rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
            exact buildRowOutput rest hrest
          · exact Or.inl ((List.toFinset_card_le rest).trans (by omega))

private theorem buildRowsBinary (rows : List (List α)) :
    BinaryUnions (rows.flatMap buildRow) := by
  induction rows with
  | nil => simp [BinaryUnions]
  | cons row rows ih => exact binaryUnionsAppend (buildRowBinary row) ih

theorem sharedIncidenceUnionConstruction {q N : ℕ} (line : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hdegree : ∀ l, (line l).card = q + 1) :
    ∃ xs : List (Finset (Fin N)), xs.length = N * q ∧ (∀ l, line l ∈ xs) ∧
      (∀ j S, xs[j]? = some S → ∃ A B : Finset (Fin N), S = A ∪ B ∧
        (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j)) := by
  let rows := (List.finRange N).map (fun l => (line l).toList)
  refine ⟨rows.flatMap buildRow, ?_, ?_, buildRowsBinary rows⟩
  · simp [rows, List.length_flatMap, List.map_map, Function.comp_def, buildRowLength, hdegree]
  · intro l
    apply List.mem_flatMap.mpr
    refine ⟨(line l).toList, by simp [rows], ?_⟩
    have h := buildRowOutput (line l).toList (by simp [hdegree]; omega)
    simpa using h

theorem sharedIncidenceUnionBudget {q N : ℕ} (line : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hdegree : ∀ l, (line l).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ line l ∧ p' ∈ line l)
    (budget : ℕ) :
    (∃ xs : List (Finset (Fin N)), xs.length ≤ budget ∧ (∀ l, line l ∈ xs) ∧
      (∀ j S, xs[j]? = some S → ∃ A B : Finset (Fin N), S = A ∪ B ∧
        (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j))) ↔ N * q ≤ budget := by
  constructor
  · rintro ⟨xs, hlength, hout, hxs⟩
    exact (sharedIncidenceUnionBound line hdegree hunique xs hxs hout).trans hlength
  · intro h
    obtain ⟨xs, hlength, hout, hxs⟩ := sharedIncidenceUnionConstruction line hq hdegree
    exact ⟨xs, hlength ▸ h, hout, hxs⟩

open PEqualNP.CircuitLowerBounds

theorem markingDoesNotChangeBound (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) :
    let singleton (p i : Fin N) : Bool := decide (i = p)
    let wire (w : ℕ) (p l : Fin N) :=
      (C.wires (List.ofFn (singleton p) ++ List.ofFn (singleton l))).getD w false
    let product (a b : ℕ) (p l : Fin N) := wire a p l && wire b p l
    (∀ marked : Finset ℕ,
      (∀ (j : ℕ) (g : Gate) (a b : ℕ),
        C.gates[j]? = some g → g.op = .and → g.inputs = [a, b] → j ∉ marked →
        (∃ w ∈ [a, b], ∀ p l, product a b p l = wire w p l) ∨
          ((∀ p l, product a b p l = true → I p l) →
            ∀ p p' l l', product a b p l = true → product a b p' l' = true → p = p' ∨ l = l')) →
      100 * marked.card < N * q → N * q ≤ 100 * C.size) ↔ N * q ≤ 100 * C.size := by
  intro singleton wire product
  constructor
  · intro h
    by_contra! hsmall
    have hbudget : 100 * (Finset.range C.size).card < N * q := by simpa using hsmall
    apply (Nat.not_le_of_gt hsmall) (h (Finset.range C.size) ?_ hbudget)
    intro j g _ _ hj _ _ hmark
    have hj' : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).choose
    exact (hmark (Finset.mem_range.mpr hj')).elim
  · intro h _ _ _
    exact h

end PEqualNP.Outside.L_meta_2866
