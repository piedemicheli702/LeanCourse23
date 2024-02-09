import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.ZFC.Basic
import LeanCourse.Common

variable {α : Type}
namespace ZFSet

def OrdTrans (X : ZFSet) : Prop :=
  IsTransitive X ∧ ∀ x ∈ X, IsTransitive x

def IsFounded (X : ZFSet) : Prop :=
  ∀ x, x ⊆ X → x ≠ ∅ → ∃ y ∈ x, ¬∃ w ∈ x, w ∈ y

def IsWellOrdered (X : ZFSet) : Prop :=
  IsFounded X ∧ ∀ x ∈ X, ∀ y ∈ X, (x ∈ y ∨ x = y ∨ y ∈ x)

def OrdVonNeumann (X : ZFSet) : Prop :=
  IsWellOrdered X ∧ IsTransitive X

def succ (X : ZFSet) : ZFSet :=
  X ∪ {X}

def IsInitialSegment (X Y : ZFSet) : Prop :=
  Y ⊆ X ∧ ∀ t ∈ Y, ∀ s, s ∈ t → s ∈ Y

lemma empty_ordTrans : OrdTrans ∅ := by {
  unfold OrdTrans
  constructor
  · exact empty_isTransitive
  · intro x hx
    by_contra
    have : x ∉ ∅ := by apply not_mem_empty
    contradiction
}

lemma empty_ordVonNeumann : OrdVonNeumann ∅ := by {
  rw [OrdVonNeumann]
  constructor
  · rw [IsWellOrdered]
    constructor
    · rw [IsFounded]
      intro x hx hnem
      have : x = ∅ := by {
         rw [eq_empty]
         have : ∀ (y : ZFSet), y ∉ ∅ := by {
          apply not_mem_empty
         }
         rw [subset_def] at hx
         by_contra h
         push_neg at h
         obtain ⟨y, hy⟩ := h
         apply hx at hy
         apply this at hy
         assumption
      }
      have fls : False := by exact hnem this
      exfalso
      assumption
    · intro x hx
      exfalso
      have : ∀ (y : ZFSet), y ∉ ∅ := by {
        apply not_mem_empty
      }
      apply this at hx
      assumption
  · exact empty_isTransitive
}

lemma ordVonNeumann_mem_empty (X : ZFSet) (hX : OrdVonNeumann X) (hnem : X ≠ ∅) : ∅ ∈ X := by {
  apply regularity at hnem
  obtain ⟨y, hy1, hy2⟩ := hnem
  have : y ⊆ X := by {
    apply hX.2
    exact hy1
  }
  rw [subset_def] at this
  rw [eq_empty] at hy2
  by_cases y = ∅
  · rw [←h]
    assumption
  · rw [eq_empty] at h
    push_neg at h
    obtain ⟨z, hz⟩ := h
    have hz1 : z ∈ y := by assumption
    apply this at hz1
    exfalso
    apply hy2 z
    rw [mem_inter]
    constructor <;> assumption
}

lemma ordTrans_mem (X Y : ZFSet) (hX : OrdTrans X) (hY : Y ∈ X) : OrdTrans Y := by {
  constructor
  · intro y hy z hz
    apply hX.2 at hY
    apply hY at hy
    apply hy
    assumption
  · intro x hx y hy z hz
    apply hX.1 at hx
    · apply hX.2 at hx
      apply hx at hy
      apply hy
      assumption
    · assumption
}

lemma ordTrans_mem_empty (X : ZFSet) (hX : OrdTrans X) (hnem : X ≠ ∅) : ∅ ∈ X := by {
  by_contra h
  apply regularity at hnem
  obtain ⟨y, hya, hyb⟩ := hnem
  rw [eq_empty] at hyb
  have : y ⊆ X := by {
    apply hX.1
    exact hya
  }
  by_cases hyp : y = ∅
  · rw [hyp] at hya
    contradiction
  · rw [eq_empty] at hyp
    push_neg at hyp
    obtain ⟨z, hz⟩ := hyp
    have this₀ : z ∈ X := by exact this hz
    apply hyb z
    rw [mem_inter]
    constructor <;> assumption
}
lemma ordTrans_mem_of_mem_of_mem (X Y Z : ZFSet) (hX : OrdTrans X) (hY : OrdTrans Y) (hZ : OrdTrans Z) : X ∈ Y → Y ∈ Z → X ∈ Z := by {
  intro h₀ h₁
  apply hZ.1 at h₁
  apply h₁ at h₀
  assumption
}

lemma succ_ordTrans {X : ZFSet} (h : OrdTrans X) : OrdTrans (succ X) := by {
  unfold OrdTrans IsTransitive
  constructor
  · intro y hy z hz
    apply ZFSet.mem_union.2
    apply ZFSet.mem_union.1 at hy
    rcases hy with hy_1 | hy_2
    · left
      rw [OrdTrans] at h
      apply h.1 at hy_1
      exact hy_1 hz
    · left
      have : y = X := by exact mem_singleton.mp hy_2
      rwa [this] at hz
  · intro x hx y hy
    apply ZFSet.mem_union.1 at hx
    rcases hx with hx_1 | hx_2
    · have : IsTransitive x := by
        apply h.2 at hx_1
        assumption
      exact this y hy
    · have : x = X := by exact mem_singleton.mp hx_2
      rw [this] at hy
      rw [this]
      apply h.1 at hy
      assumption
}

lemma union_singleton_of_mem {X Y : ZFSet} (h : X ∪ {X} = Y) : X ∈ Y := by {
  rw [←h]
  apply mem_union.2
  right
  exact mem_singleton.mpr rfl
}

lemma eq_of_subset_and_subset (X Y : ZFSet) (h₁ : X ⊆ Y) (h₂ : Y ⊆ X) : X = Y := by {
  apply ext_iff.2
  intro z
  constructor
  · intro hz
    apply h₁
    assumption
  · intro hz
    apply h₂
    assumption
}

theorem ordTrans_mem_or_eq_or_mem (X Y : ZFSet) : OrdTrans X → OrdTrans Y → (X ∈ Y ∨ X = Y ∨ Y ∈ X) := by {
  intro hX hY
  by_contra h
  push_neg at h
  let p := fun z => (z ∉ Y ∧ z ≠ Y ∧ Y ∉ z)
  let M := ZFSet.sep p (succ X)
  have : M ≠ ∅ := by {
    rw [Ne]
    rw [eq_empty]
    push_neg
    use X
    rw [mem_sep]
    constructor
    · rw [succ]
      rw [mem_union]
      right
      exact mem_singleton.mpr rfl
    · exact h
  }
  apply regularity at this
  obtain ⟨y, hya, hyb⟩ := this
  have hsub1: y ⊆ Y := by {
    intro z hz
    have : z ∈ Y ∨ z = Y ∨ Y ∈ z := by {
      by_contra H
      push_neg at H
      have : z ∈ M := by {
        rw [mem_sep]
        constructor
        · have : OrdTrans (succ X) := by exact succ_ordTrans hX
          rw [mem_sep] at hya
          have hyaa : y ∈ succ X := by exact hya.1
          apply this.1 at hyaa
          apply hyaa at hz
          assumption
        · exact H
      }
      rw [eq_empty] at hyb
      apply hyb z
      rw [mem_inter]
      constructor <;> assumption
    }
    rcases this with H | H | H
    · assumption
    · rw [H] at hz
      rw [mem_sep] at hya
      exfalso
      have hyaa : p y := by exact hya.2
      have : y ∉ Y ∧ y ≠ Y ∧ Y ∉ y := by exact hyaa
      have : Y ∉ y := by exact this.2.2
      contradiction
    · have hyp : OrdTrans y := by {
        have : y ∈ succ X := by {
          rw [mem_sep] at hya
          exact hya.1
        }
        apply ordTrans_mem (succ X)
        exact succ_ordTrans hX
        assumption
      }
      have hyp2 : OrdTrans z := by {
        apply ordTrans_mem y <;> assumption
      }
      have hyp3 : Y ∈ y := by {
        apply ordTrans_mem_of_mem_of_mem Y z <;> assumption
      }
      rw [mem_sep] at hya
      have hyaa : p y := by exact hya.2
      have : y ∉ Y ∧ y ≠ Y ∧ Y ∉ y := by exact hyaa
      have : Y ∉ y := by exact this.2.2
      exfalso
      contradiction
  }
  let q := fun z => (z ∉ X ∧ z ≠ X ∧ X ∉ z)
  let N := ZFSet.sep q (succ Y)
  have : N ≠ ∅ := by {
    rw [Ne]
    rw [eq_empty]
    push_neg
    use Y
    rw [mem_sep]
    constructor
    · rw [succ]
      rw [mem_union]
      right
      exact mem_singleton.mpr rfl
    · constructor
      · exact h.2.2
      · constructor
        · apply Ne.symm
          exact h.2.1
        · exact h.1
  }
  apply regularity at this
  obtain ⟨w, hwa, hwb⟩ := this
  have hsub2 : w ⊆ X := by {
    intro z hz
    have : z ∈ X ∨ z = X ∨ X ∈ z := by {
      by_contra H
      push_neg at H
      have : z ∈ N := by {
        rw [mem_sep]
        constructor
        · rw [mem_sep] at hwa
          have : OrdTrans (succ Y) := by exact succ_ordTrans hY
          have this₀ : w ⊆ (succ Y) := by {
            have H' : w ∈ succ Y := by exact hwa.1
            apply this.1 at H'
            assumption
          }
          apply this₀ at hz
          assumption
        · exact H
      }
      rw [eq_empty] at hwb
      apply hwb z
      rw [mem_inter]
      constructor <;> assumption
    }
    rcases this with H | H | H
    · assumption
    · rw [H] at hz
      rw [mem_sep] at hwa
      exfalso
      have hwaa : q w := by exact hwa.2
      have : X ∉ w := by exact hwaa.2.2
      contradiction
    · have : OrdTrans w := by {
        rw [mem_sep] at hwa
        have : OrdTrans (succ Y) := by exact succ_ordTrans hY
        have hwaa : w ∈ succ Y := by exact hwa.1
        apply ordTrans_mem (succ Y) <;> assumption
      }
      have this₀ : OrdTrans z := by {
        apply ordTrans_mem w <;> assumption
      }
      have this₁ : X ∈ w := by exact ordTrans_mem_of_mem_of_mem X z w hX this₀ this H hz
      rw [mem_sep] at hwa
      have hwaa : q w := by exact hwa.2
      have : X ∉ w := by exact hwaa.2.2
      exfalso
      contradiction
  }
  sorry
}

lemma subset_of_wellordered (X Y : ZFSet) (hX : IsWellOrdered X) (hY : Y ⊆ X) : IsWellOrdered Y := by {
  rw [IsWellOrdered]
  rw [IsWellOrdered] at hX
  constructor
  · rw [IsFounded]
    intro x hx hnem
    apply regularity at hnem
    obtain ⟨z, hza, hzb⟩ := hnem
    use z
    constructor
    · exact hza
    · push_neg
      intro w hw
      rw [eq_empty] at hzb
      have : w ∉ x ∩ z := by exact hzb w
      by_contra h
      have this₀ : w ∈ x ∩ z := by {
        rw [mem_inter]
        constructor <;> assumption
      }
      contradiction
  · intro v hv
    have : v ∈ X := by {
      apply hY
      assumption
    }
    intro y hy
    have this₀ : y ∈ X := by {
      apply hY
      assumption
    }
    apply hX.2 <;> assumption
}

lemma ordTrans_pair_union (X Y : ZFSet) (hX : OrdTrans X) (hY : OrdTrans Y) : OrdTrans (X ∪ Y) := by {
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    rw [OrdTrans] at hX hY
    intro y hy y₀ hy₀
    have hyp : y ∈ X ∨ y ∈ Y := by exact mem_union.mp hy
    rcases hyp with h | h
    · apply hX.1 at h
      apply h at hy₀
      rw [mem_union]
      left
      assumption
    · apply hY.1 at h
      apply h at hy₀
      rw [mem_union]
      right
      assumption
  · intro x hx
    rw [IsTransitive]
    intro y hy
    rw [OrdTrans] at hX hY
    have hyp : x ∈ X ∨ x ∈ Y := by exact mem_union.mp hx
    rcases hyp with h | h
    · apply hX.2 <;> assumption
    · apply hY.2 <;> assumption
}

lemma ordTrans_pair_inter (X Y : ZFSet) (hX : OrdTrans X) (hY : OrdTrans Y) : OrdTrans (X ∩ Y) := by {
  rw [OrdTrans]
  constructor
  · rw [OrdTrans] at hX hY
    rw [IsTransitive]
    rw [IsTransitive] at hX hY
    intro y hy
    have hyp1 : y ⊆ X := by {
      apply hX.1
      rw [mem_inter] at hy
      exact hy.1
    }
    have hyp2 : y ⊆ Y := by {
      apply hY.1
      rw [mem_inter] at hy
      exact hy.2
    }
    intro z hz
    have hz1 : z ∈ X := by exact hyp1 hz
    have hz2 : z ∈ Y := by exact hyp2 hz
    apply mem_inter.2
    constructor <;> assumption
  · intro x hx
    rw [OrdTrans] at hX hY
    have : x ∈ X := by {
      rw [mem_inter] at hx
      exact hx.1
    }
    apply hX.2 at this
    assumption
}

lemma succ_subset_of_mem (X Y : ZFSet) (hX : OrdTrans X) (hY : OrdTrans Y) : X ∈ Y → succ X ⊆ Y := by {
  intro hmem
  have : X ≠ Y := by {
    by_contra h
    rw [h] at hmem
    apply mem_irrefl at hmem
    assumption
  }
  intro z hz
  rw [succ] at hz
  rw [mem_union] at hz
  rw [OrdTrans] at hY
  rcases hz with hz | hz
  · apply hY.1 at hmem
    exact hmem hz
  · have : z = X := by exact mem_singleton.mp hz
    rw [this]
    assumption
}

lemma ordTrans_sUnion (X : ZFSet) (hX : ∀ x ∈ X, OrdTrans x) : OrdTrans (⋃₀ X) := by {
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    intro y hy
    rw [mem_sUnion] at hy
    intro a ha
    obtain ⟨z, hz1, hz2⟩ := hy
    have : a ∈ z := by {
      apply hX at hz1
      rw [OrdTrans] at hz1
      rw [IsTransitive] at hz1
      have : y ⊆ z := by {
        apply hz1.1 at hz2
        assumption
      }
      exact this ha
    }
    apply mem_sUnion_of_mem this
    assumption
  · intro x hx
    rw [IsTransitive]
    intro y hy z hz
    rw [mem_sUnion] at hx
    obtain ⟨a, ha1, ha2⟩ := hx
    apply hX at ha1
    rw [OrdTrans] at ha1
    apply ha1.2 at ha2
    rw [IsTransitive] at ha2
    have : y ⊆ x := by {
      exact ha2 y hy
    }
    exact ha2 y hy hz
}

lemma ordTrans_sInter {X : ZFSet} (hX : ∀ x ∈ X, OrdTrans x) (hXnem : X ≠ ∅) : OrdTrans (⋂₀ X) := by {
  rw [OrdTrans]
  constructor
  · rw [IsTransitive]
    intro y hy z hz
    rw [mem_sInter]
    · intro a ha
      have hyp₀ : y ∈ a := by {
        exact mem_of_mem_sInter hy ha
      }
      have hyp₁ : OrdTrans a := by exact hX a ha
      have hyp₂ : y ⊆ a  := by {
        rw [OrdTrans] at hyp₁
        rw [IsTransitive] at hyp₁
        apply hyp₁.1
        assumption
      }
      exact hyp₂ hz
    · rw [nonempty_def]
      rw [Ne] at hXnem
      rw [eq_empty] at hXnem
      push_neg at hXnem
      exact hXnem
  · intro x hx
    rw [IsTransitive]
    intro y hy a ha
    have : ∃ z ∈ X, x ∈ z := by {
      have : ∃ w, w ∈ X := by {
        rw [Ne] at hXnem
        rw [eq_empty] at hXnem
        push_neg at hXnem
        exact hXnem
      }
      obtain ⟨w, hw⟩ := this
      use w
      constructor
      · assumption
      · exact mem_of_mem_sInter hx hw
    }
    obtain ⟨z, hz1, hz2⟩ := this
    apply hX at hz1
    rw [OrdTrans] at hz1
    apply hz1.2 at hz2
    exact hz2 y hy ha
}

lemma ordTrans_iff_ordTrans_and_trans (X : ZFSet) : OrdTrans X ↔ ((∀ x ∈ X, OrdTrans x) ∧ IsTransitive X) := by {
  constructor
  · intro hX
    constructor
    · intro x hx
      exact ordTrans_mem X x hX hx
    · exact hX.1
  · intro h
    rw [OrdTrans]
    constructor
    · exact h.2
    · intro x hx
      apply h.1 at hx
      exact hx.1
}

theorem burali_forti : ¬∃ (X : ZFSet), ∀ x, OrdTrans x ↔ x ∈ X := by {
  by_contra h
  obtain ⟨X, hX⟩ := h
  have htrans : IsTransitive X := by {
    intro x hx z hz
    have : OrdTrans x := by {
      rw [hX]
      assumption
    }
    have : OrdTrans z := by {
      exact ordTrans_mem x z this hz
    }
    rw [hX] at this
    assumption
  }
  have : OrdTrans X := by {
    rw [ordTrans_iff_ordTrans_and_trans]
    constructor
    · intro x hx
      rw [←hX] at hx
      assumption
    · assumption
  }
  have : X ∈ X := by {
    rw [← hX]
    assumption
  }
  apply mem_irrefl X
  assumption
}

lemma ordVonNeumann_mem (X Y : ZFSet) (hX : OrdVonNeumann X) (hY : Y ∈ X) : OrdVonNeumann Y := by {
  by_cases Y = ∅
  · rw [h]
    exact empty_ordVonNeumann
  · rw [OrdVonNeumann]
    rw [OrdVonNeumann] at hX
    constructor
    · rw [IsWellOrdered]
      constructor
      rotate_right
      · have : Y ⊆ X := by {
          apply hX.2
          assumption
        }
        rw [subset_def] at this
        intro x hx y hy
        apply this at hx
        apply this at hy
        rw [IsWellOrdered] at hX
        apply hX.1.2 <;> assumption
      · rw [IsFounded]
        intro x hx hnem
        apply regularity at hnem
        obtain ⟨y, hy1, hy2⟩ := hnem
        use y
        constructor
        · exact hy1
        · push_neg
          intro w hw
          by_contra hyp
          have : w ∈ x ∩ y := by {
            apply mem_inter.2
            constructor <;> assumption
          }
          rw [eq_empty] at hy2
          apply hy2 w
          assumption
    · intro x hx y hy
      have hx₀ : x ∈ X := by {
        apply hX.2 at hY
        apply hY at hx
        assumption
      }
      have hy₀ : y ∈ X := by {
        apply hX.2 at hx₀
        apply hx₀
        assumption
      }
      rw [IsWellOrdered] at hX
      apply hX.1.2 at hY
      apply hY at hy₀
      rcases hy₀ with hy₀ | hy₀ | hy₀
      · apply hY at hx₀
        rcases hx₀ with hx₀ | hx₀ | hx₀
        · apply mem_asymm at hx₀
          exfalso
          contradiction
        · rw [hx₀]
          exact hy
        · exfalso
          have : {x, y, Y} ≠ ∅ := by {
            rw [Ne]
            rw [eq_empty]
            push_neg
            use x
            apply mem_insert x {y, Y}
          }
          apply regularity at this
          obtain ⟨z, hza, hzb⟩ := this
          rw [eq_empty] at hzb
          rw [mem_insert_iff] at hza
          rcases hza with hza | hza
          · apply hzb y
            rw [mem_inter]
            constructor
            · rw [mem_insert_iff]
              right
              rw [mem_insert_iff]
              left
              rfl
            · rw [hza]
              assumption
          · rw [mem_insert_iff] at hza
            rcases hza with hza | hza
            · apply hzb Y
              rw [mem_inter]
              constructor
              · rw [mem_insert_iff]
                right
                rw [mem_insert_iff]
                right
                exact mem_singleton.mpr rfl
              · rw [hza]
                exact hy₀
            · have : z = Y := by exact mem_singleton.mp hza
              apply hzb x
              rw [mem_inter]
              constructor
              · rw [mem_insert_iff]
                left
                rfl
              · rw [this]
                exact hx₀
      · rw [←hy₀] at hy
        exfalso
        apply mem_asymm at hx
        contradiction
      · assumption
}

lemma diff_neq_empty_of_subset (X Y : ZFSet) (h₀ : Y ⊆ X) (h₁ : Y ≠ X) : X \ Y ≠ ∅ := by {
  rw [subset_def] at h₀
  rw [Ne] at h₁
  rw [ext_iff] at h₁
  push_neg at h₁
  rw [Ne]
  rw [eq_empty]
  push_neg
  obtain ⟨z, hz⟩ := h₁
  rcases hz with hz | hz
  · exfalso
    have hz1 : z ∈ Y := by exact hz.1
    apply h₀ at hz1
    apply hz.2
    assumption
  · use z
    rw [mem_diff]
    constructor
    · exact hz.2
    · exact hz.1
}

lemma mem_or_eq_of_init (X Y : ZFSet) (hX : OrdVonNeumann X) (hinit : IsInitialSegment X Y) : Y ∈ X ∨ Y = X := by {
  unfold IsInitialSegment at hinit
  by_cases X = Y
  · right
    rw [h]
  · push_neg at h
    by_cases hyp : Y = ∅
    · rw [hyp]
      left
      rw [hyp] at h
      apply ordVonNeumann_mem_empty <;> assumption
    · left
      have : X \ Y ≠ ∅ := by {
        apply diff_neq_empty_of_subset
        · exact hinit.1
        · exact id (Ne.symm h)
      }
      apply regularity at this
      obtain ⟨y, hy⟩ := this
      have : y = Y := by {
        rw [ext_iff]
        intro z
        constructor
        · intro hz
          have hzcopy : z ∈ y := by exact hz
          have : y ∈ X := by {
            have : y ∈ X \ Y := by exact hy.1
            rw [mem_diff] at this
            exact this.left
          }
          apply hX.2 at this
          apply this at hz
          by_contra h'
          have hyp' : z ∈ X \ Y := by {
            rw [mem_diff]
            constructor <;> assumption
          }
          have hyp'' : z ∈ X \ Y ∩ y := by {
            rw [mem_inter]
            constructor <;> assumption
          }
          rw [hy.2] at hyp''
          apply not_mem_empty at hyp''
          assumption
        · intro hz
          have : z ∈ X := by {
            apply hinit.1 hz
          }
          rw [OrdVonNeumann] at hX
          rw [IsWellOrdered] at hX
          have H : z ∈ y ∨ z = y ∨ y ∈ z := by {
            apply hX.1.2
            · assumption
            · have : y ∈ X \ Y := by exact hy.1
              rw [mem_diff] at this
              exact this.1
          }
          rcases H with H | H | H
          · assumption
          · rw [H] at hz
            have hyn : y ∉ Y := by {
              have : y ∈ X \ Y := by exact hy.1
              rw [mem_diff] at this
              exact this.2
            }
            exfalso
            contradiction
          · apply hinit.2 at hz
            apply hz at H
            have hyn : y ∉ Y := by {
              have : y ∈ X \ Y := by exact hy.1
              rw [mem_diff] at this
              exact this.2
            }
            exfalso
            contradiction
      }
      rw [←this]
      have : y ∈ X \ Y := by exact hy.1
      rw [mem_diff] at this
      exact this.1
}

def SuccOrdVN (X : ZFSet) : Prop :=
  OrdVonNeumann X ∧ ∃ Y, (OrdVonNeumann Y ∧ succ Y = X)

def LimOrdVN (X : ZFSet) : Prop :=
  OrdVonNeumann X ∧ (¬ ∃ Y, (OrdVonNeumann Y ∧ succ Y = X)) ∧ X ≠ ∅

theorem ordVonNeumann_empty_or_succ_or_lim (X : ZFSet) (hX : OrdVonNeumann X) : X = ∅ ∨ SuccOrdVN X ∨ LimOrdVN X := by {
  have hXa : OrdVonNeumann X := by exact hX
  by_contra hnX
  push_neg at hnX
  rcases hnX with ⟨hnem, hnsucc, hnlim⟩
  unfold SuccOrdVN at hnsucc
  push_neg at hnsucc
  unfold LimOrdVN at hnlim
  push_neg at hnlim
  apply hnsucc at hX
  apply hnlim at hX
  · contradiction
  · exact hXa
}

theorem ordVonNeumann_induction1 (p : ZFSet → Prop) (h : ∀ (Z : ZFSet), OrdVonNeumann Z → (∀ (Y : ZFSet), (Y ∈ Z → p Y)) → p Z): ∀ X, OrdVonNeumann X → p X := by {
  by_contra hyp
  push_neg at hyp
  obtain ⟨X, hXa, hXb⟩ := hyp
  by_cases hyp : X = ∅
  · apply h at hXa
    rw [eq_empty] at hyp
    apply hXb
    apply hXa
    intro Y hY
    have : Y ∉ X := by exact hyp Y
    exfalso
    contradiction
  · rw [eq_empty] at hyp
    push_neg at hyp
    have hXacopy : OrdVonNeumann X := by exact hXa
    apply h at hXa
    have : ∃ (Y : ZFSet), Y ∈ X ∧ ¬ p Y := by {
      by_contra H
      push_neg at H
      apply hXa at H
      contradiction
    }
    obtain ⟨Y, hY⟩ := this
    let q := fun x ↦ ¬ p x
    let A := ZFSet.sep q X
    have hiff : q Y ↔ ¬ p Y := by exact Iff.rfl
    have : A ≠ ∅ := by {
      rw [Ne]
      rw [eq_empty]
      push_neg
      use Y
      rw [mem_sep]
      constructor
      · exact hY.1
      · rw [hiff]
        exact hY.2
    }
    apply regularity at this
    obtain ⟨w, hw1, hw2⟩ := this
    have : ∀ v ∈ w, p v := by {
      intro v hv
      by_contra Hv
      have : v ∈ A := by {
        rw [mem_sep]
        constructor
        · rw [mem_sep] at hw1
          apply hXacopy.2 w
          exact hw1.1
          exact hv
        · have : q v ↔ ¬ p v := by rw [@not_iff_not]
          rw [this]
          exact Hv
      }
      rw [eq_empty] at hw2
      apply hw2 v
      rw [mem_inter]
      constructor <;> assumption
    }
    have this₀ : OrdVonNeumann w := by {
      have : w ∈ X := by {
        rw [mem_sep] at hw1
        exact hw1.1
      }
      exact ordVonNeumann_mem X w hXacopy this
    }
    apply h at this₀
    apply this₀ at this
    rw [mem_sep] at hw1
    have this₁ : ¬ p w := by {
      have : ¬ p w ↔ q w := by exact Iff.rfl
      rw [this]
      exact hw1.2
    }
    contradiction
}

theorem succ_ordVonNeumann  (X : ZFSet) (hX : OrdVonNeumann X) : OrdVonNeumann (succ X) := by {
  unfold OrdVonNeumann
  constructor
  · unfold IsWellOrdered
    constructor
    · unfold IsFounded
      intro x hx hnem
      apply regularity at hnem
      obtain ⟨y, hya, hyb⟩ := hnem
      use y
      constructor
      · assumption
      · by_contra h
        obtain ⟨w, hw⟩ := h
        rw [eq_empty] at hyb
        rw [←mem_inter] at hw
        apply hyb at hw
        assumption
    · intro x hx y hy
      rw [succ] at hx hy
      rw [mem_union] at hx hy
      rcases hx with hx | hx
      · rcases hy with hy | hy
        · apply hX.1.2 <;> assumption
        · rw [mem_singleton] at hy
          rw [hy]
          left
          assumption
      · rcases hy with hy | hy
        · rw [mem_singleton] at hx
          rw [hx]
          right
          right
          assumption
        · rw [mem_singleton] at hx hy
          rw [hx]
          rw [hy]
          right
          left
          rfl
  · unfold IsTransitive
    intro y hy z hz
    rw [succ]
    rw [succ] at hy
    rw [mem_union]
    rw [mem_union] at hy
    rcases hy with hy | hy
    · left
      apply hX.2 at hy
      apply hy
      assumption
    · left
      rw [mem_singleton] at hy
      rw [←hy]
      assumption
}

theorem ordVonNeumann_induction2 (p : ZFSet → Prop) (X : ZFSet) (hX : OrdVonNeumann X) (hem : p ∅) (hsucc : ∀ Z, OrdVonNeumann Z → p Z → p (succ Z)) (hlim : ∀ Z, LimOrdVN Z → (∀ Y ∈ Z, p Y) → p Z) : p X := by {
  induction X using inductionOn
  case h X hXind
  · apply ordVonNeumann_empty_or_succ_or_lim at hX
    rcases hX with hX | hX | hX
    · rw [hX]
      exact hem
    · obtain ⟨Y, hYa, hYb⟩ := hX.2
      have : Y ∈ X := by {
        rw [←hYb]
        apply mem_union.2
        right
        exact mem_singleton.mpr rfl
      }
      apply hXind at this
      have hYacopy : OrdVonNeumann Y := by assumption
      apply hsucc at hYa
      apply this at hYacopy
      apply hYa at hYacopy
      rw [hYb] at hYacopy
      assumption
    · have hX₀ : OrdVonNeumann X := by exact hX.1
      apply hlim at hX
      apply hX
      intro Y hY
      have hYcopy : Y ∈ X := by assumption
      apply hXind at hY
      apply ordVonNeumann_mem at hYcopy
      · apply hY at hYcopy
        assumption
      · assumption
}

lemma ordVonNeumann_of_init (X Y : ZFSet) (hX : OrdVonNeumann X) (hY : IsInitialSegment X Y) : OrdVonNeumann Y := by {
  constructor
  · constructor
    rw [IsFounded]
    intro x hx hnem
    apply regularity at hnem
    obtain ⟨y, hy⟩ := hnem
    use y
    constructor
    · exact hy.1
    · push_neg
      intro w hw
      obtain h := hy.2
      by_contra H
      have : w ∈ x ∩ y := by {
        rw [mem_inter]
        constructor <;> assumption
      }
      rw [eq_empty] at h
      apply h w
      assumption
    · intro x hx y hy
      have H : x ∈ X := by {
        apply hY.1 at hx
        assumption
      }
      have H' : y ∈ X := by {
        apply hY.1 at hy
        assumption
      }
      obtain H₀ := hX.1.2
      apply H₀ <;> assumption
  · intro y hy z hz
    apply hY.2 y <;> assumption
}

lemma eq_empty_of_subset {X : ZFSet} : X ⊆ ∅ → X = ∅ := by {
  intro h
  rw [ZFSet.subset_def] at h
  rw [eq_empty]
  intro y hy
  apply h at hy
  apply not_mem_empty at hy
  assumption
}


lemma mem_or_eq_of_initVN (X Y : ZFSet) (hX : OrdVonNeumann X) (hY : IsInitialSegment X Y) : Y ∈ X ∨ Y = X := by {
  by_cases Y = X
  · right
    assumption
  · have : OrdVonNeumann Y := by exact ordVonNeumann_of_init X Y hX hY
    left
    have H : ∀ Z ∈ X, Z ∈ Y ∨ ∀ x ∈ Y, x ∈ Z := by {
      intro Z hZ
      by_cases H : Z ∈ Y
      · left
        assumption
      · right
        intro x hx
        apply mem_or_eq_of_init at hY
        rcases hY with hY | hY
        rotate_left
        · rw [hY] at H
          exfalso
          contradiction
        · assumption
        · have : Y = Z ∨ Y ∈ Z := by {
            obtain hyp := hX.1.2
            apply hyp at hY
            apply hY at hZ
            by_contra H₀
            push_neg at H₀
            have H₁ : Y ∉ Z ∧ Y ≠ Z ∧ Z ∉ Y := by {
              constructor
              · exact H₀.2
              · constructor
                · exact H₀.1
                · assumption
            }
            rcases hZ with hZ | hZ | hZ
            · obtain H₁ := H₁.1
              contradiction
            · obtain H₁ := H₁.2.1
              contradiction
            · obtain H₁ := H₁.2.2
              contradiction
          }
          rcases this with hyp | hyp
          · rw [←hyp]
            assumption
          · have this₀ : OrdVonNeumann Z := by exact ordVonNeumann_mem X Z hX hZ
            apply this₀.2 Y <;> assumption
    }
    have H' : ∃ Z ∈ X, Y ⊆ Z := by {
      use Y
      constructor
      · apply mem_or_eq_of_init at hY
        rcases hY with hY | hY
        · assumption
        · exfalso
          contradiction
        · assumption
      · rfl
    }
    let p := fun x ↦ x ∈ X ∧ Y ⊆ x
    let A := ZFSet.sep p X
    have this₀ : A ≠ ∅ := by {
      rw [Ne]
      rw [eq_empty]
      push_neg
      obtain ⟨Z, hZ⟩ := H'
      use Z
      rw [mem_sep]
      constructor
      · exact hZ.1
      · exact hZ
    }
    apply regularity at this₀
    obtain ⟨w, hwa, hwb⟩ := this₀
    by_cases h' : Y = w
    · rw [h']
      rw [mem_sep] at hwa
      exact hwa.1
    · have h₀ : ∃ v ∈ w, Y ⊆ v := by {
         use Y
         constructor
         · obtain hwo := hX.1.2
           have this₂ : w ∈ X := by {
            rw [mem_sep] at hwa
            exact hwa.1
           }
           apply hwo at this₂
           have this₁ : Y ∈ X := by {
            apply mem_or_eq_of_init at hY
            rcases hY with hY | hY
            · assumption
            · exfalso
              contradiction
            · assumption
           }
           apply this₂ at this₁
           rcases this₁ with hm | hm | hm
           · have this₃ : Y ⊆ w := by {
              rw [mem_sep] at hwa
              obtain hwaa := hwa.2
              exact hwaa.2
             }
             apply this₃ at hm
             have this₄ : w ∉ w := by exact mem_asymm hm
             exfalso
             contradiction
           · exfalso
             exact h' (id hm.symm)
           · assumption
         · rfl
      }
      obtain ⟨v, hva, hvb⟩ := h₀
      have h₀ : v ∈ A := by {
        rw [mem_sep]
        constructor
        · have h₀ : w ∈ X := by {
            rw [mem_sep] at hwa
            exact hwa.1
          }
          apply hX.2 w <;> assumption
        · constructor
          · have h₀ : w ∈ X := by {
              rw [mem_sep] at hwa
              exact hwa.1
            }
            apply hX.2 w <;> assumption
          · assumption
      }
      have h₁ : v ∈ A ∩ w := by {
        rw [mem_inter]
        constructor <;> assumption
      }
      exfalso
      rw [hwb] at h₁
      have h₂ : v ∉ ∅ := by {
        apply not_mem_empty
      }
      contradiction
}

/-Trichotomy of Ordinals -/
lemma ordVonNeumann_mem_or_eq_or_mem (X Y : ZFSet) (hX : OrdVonNeumann X) (hY : OrdVonNeumann Y) : X ∈ Y ∨ X = Y ∨ Y ∈ X := by {
  let A := X ∩ Y
  have thisX : IsInitialSegment X A := by {
    rw [IsInitialSegment]
    constructor
    · intro z hz
      rw [mem_inter] at hz
      exact hz.1
    · intro t ht s hs
      rw [mem_inter]
      constructor
      · have : t ∈ X := by {
          rw [mem_inter] at ht
          exact ht.1
        }
        apply hX.2 at this
        apply this
        assumption
      · have : t ∈ Y := by {
          rw [mem_inter] at ht
          exact ht.2
        }
        apply hY.2 at this
        apply this
        assumption
  }
  have thisY : IsInitialSegment Y A := by {
    rw [IsInitialSegment]
    constructor
    · intro z hz
      rw [mem_inter] at hz
      exact hz.2
    · intro t ht s hs
      rw [mem_inter]
      constructor
      · have : t ∈ X := by {
          rw [mem_inter] at ht
          exact ht.1
        }
        apply hX.2 at this
        apply this
        assumption
      · have : t ∈ Y := by {
          rw [mem_inter] at ht
          exact ht.2
        }
        apply hY.2 at this
        apply this
        assumption
  }
  have h₀ : A ∈ X ∨ A = X := by {
    apply mem_or_eq_of_init <;> assumption
  }
  have h₁ : A ∈ Y ∨ A = Y := by {
    apply mem_or_eq_of_init <;> assumption
  }
  rcases h₀ with h₀ | h₀
  · rcases h₁ with h₁ | h₁
    · have : A ∈ A := by {
        rw [mem_inter]
        constructor <;> assumption
      }
      have this₁ : A ∉ A := by exact mem_asymm this
      contradiction
    · right
      right
      rw [←h₁]
      assumption
  · rcases h₁ with h₁ | h₁
    · left
      rw [←h₀]
      assumption
    · right
      left
      rw [←h₀]
      assumption
}

lemma ordVonNeumann_sUnion (X : ZFSet) (hX : ∀ x ∈ X, OrdVonNeumann X) : OrdVonNeumann (⋃₀ X) := by {
  constructor
  · constructor
    · intro x hx hnem
      apply regularity at hnem
      obtain ⟨y, hya, hyb⟩ := hnem
      use y
      constructor
      · assumption
      · push_neg
        intro w hw
        by_contra h
        have : w ∈ x ∩ y := by {
          apply mem_inter.2
          constructor <;> assumption
        }
        rw [eq_empty] at hyb
        apply hyb w
        assumption
    · intro x hx y hy
      rw [mem_sUnion] at hx hy
      obtain ⟨z₀, hz₀a, hz₀b⟩ := hx
      obtain ⟨z₁, hz₁a, hz₁b⟩ := hy
      have h₀ : OrdVonNeumann z₀ := by exact ordVonNeumann_mem X z₀ (hX z₀ hz₀a) hz₀a
      have h₁ : OrdVonNeumann z₁ := by exact ordVonNeumann_mem X z₁ (hX z₀ hz₀a) hz₁a
      have hx : OrdVonNeumann x := by exact ordVonNeumann_mem z₀ x h₀ hz₀b
      have hy : OrdVonNeumann y := by exact ordVonNeumann_mem z₁ y h₁ hz₁b
      exact ordVonNeumann_mem_or_eq_or_mem x y hx hy
  · intro y hy z hz
    rw [mem_sUnion] at hy
    obtain ⟨x, hxa, hxb⟩ := hy
    have hxx : OrdVonNeumann x := by exact ordVonNeumann_mem X x (hX x hxa) hxa
    apply hxx.2 at hxb
    apply hxb at hz
    exact mem_sUnion_of_mem hz hxa
}

lemma limOrd_iff_eq_sUnion (X : ZFSet) (hX : OrdVonNeumann X) (hnem : X ≠ ∅) : LimOrdVN X ↔ X = (⋃₀ X : ZFSet) := by {
  constructor
  · intro hlim
    by_contra h
    have : (⋃₀ X : ZFSet) ⊆ X := by {
      intro x hx
      rw [mem_sUnion] at hx
      obtain ⟨z, hza, hzb⟩ := hx
      apply hX.2 at hza
      apply hza
      assumption
    }
    have : X \ (⋃₀ X : ZFSet) ≠ ∅ := by {
      apply diff_neq_empty_of_subset
      · assumption
      · exact Ne.symm h
    }
    rw [Ne] at this
    rw [eq_empty] at this
    push_neg at this
    obtain ⟨y, hy⟩ := this
    have this₀ : X ⊆ (succ y) := by {
      intro z hz
      have this₀ : OrdVonNeumann z := by exact ordVonNeumann_mem X z hX hz
      have this₁ : OrdVonNeumann y := by {
        rw [mem_diff] at hy
        obtain hyy := hy.1
        exact ordVonNeumann_mem X y hX hyy
      }
      have H : y ∈ z ∨ y = z ∨ z ∈ y := by exact ordVonNeumann_mem_or_eq_or_mem y z this₁ this₀
      rcases H with H | H | H
      · have this₂ : y ∉ z := by {
          rw [mem_diff] at hy
          rw [mem_sUnion] at hy
          obtain hyy := hy.2
          push_neg at hyy
          apply hyy at hz
          assumption
        }
        contradiction
      · rw [H]
        rw [succ]
        rw [mem_union]
        right
        rw [mem_singleton]
      · rw [succ]
        rw [mem_union]
        left
        assumption
    }
    have this₁ : succ y ⊆ X := by {
      intro z hz
      rw [succ] at hz
      rw [mem_union] at hz
      rcases hz with hz | hz
      · have H : y ∈ X := by {
          rw [mem_diff] at hy
          exact hy.1
        }
        apply hX.2 at H
        apply H
        assumption
      · rw [mem_singleton] at hz
        rw [hz]
        rw [mem_diff] at hy
        exact hy.1
    }
    have this₂ : X = succ y := by exact eq_of_subset_and_subset X (succ y) this₀ this₁
    rw [LimOrdVN] at hlim
    obtain hsucc := hlim.2.1
    apply hsucc
    use y
    constructor
    · rw [mem_diff] at hy
      obtain hyy := hy.1
      exact ordVonNeumann_mem X y hX (this₁ (this₀ hyy))
    · rw [this₂]
  · intro heq
    by_contra h
    rw [LimOrdVN] at h
    push_neg at h
    have hXc : OrdVonNeumann X := by exact hX
    apply h at hXc
    by_cases H : SuccOrdVN X
    · rw [SuccOrdVN] at H
      obtain H2 := H.2
      obtain ⟨Y, hY⟩ := H2
      have : Y ∈ X := by {
        rw [succ] at hY
        apply union_singleton_of_mem
        exact hY.2
      }
      have this₀ : ∃ Z, Z ∈ X \ ⋃₀ X := by {
        use Y
        rw [mem_diff]
        constructor
        · assumption
        · rw [mem_sUnion]
          push_neg
          intro z hz
          by_contra hyp
          obtain hYY := hY.2
          rw [←hYY] at hz
          rw [succ] at hz
          rw [mem_union] at hz
          rcases hz with hz | hz
          · have this₃ : z ∉ Y := by exact mem_asymm hyp
            contradiction
          · rw [mem_singleton] at hz
            rw [hz] at hyp
            have this₂ : Y ∉ Y := by exact mem_asymm hyp
            contradiction
      }
      obtain ⟨Z, hZ⟩ := this₀
      rw [mem_diff] at hZ
      obtain hZZ := hZ.1
      rw [ext_iff] at heq
      have this₁ : ¬ (∀ (z : ZFSet), z ∈ X ↔ z ∈ (⋃₀ X : ZFSet)) := by {
        push_neg
        use Z
        left
        assumption
      }
      contradiction
    · rw [SuccOrdVN] at H
      push_neg at H
      apply H at hX
      apply hXc at hX
      contradiction
}

lemma ordVonNeumann_sInter (X : ZFSet) (hX : ∀ x ∈ X, OrdVonNeumann X) (hnX : X ≠ ∅) : OrdVonNeumann (⋂₀ X) := by {
  constructor
  · constructor
    · intro x hx hnem
      apply regularity at hnem
      obtain ⟨y, hya, hyb⟩ := hnem
      use y
      constructor
      · assumption
      · push_neg
        intro w hw
        by_contra h
        have : w ∈ x ∩ y := by {
          apply mem_inter.2
          constructor <;> assumption
        }
        rw [eq_empty] at hyb
        apply hyb w
        assumption
    · intro x hx y hy
      rw [mem_sInter] at hx hy
      · rw [Ne] at hnX
        rw [eq_empty] at hnX
        push_neg at hnX
        obtain ⟨w, hw⟩ := hnX
        have hwc : w ∈ X := by exact hw
        have : OrdVonNeumann w := by exact ordVonNeumann_mem X w (hX w hw) hw
        apply hx at hw
        apply hy at hwc
        have hxx : OrdVonNeumann x := by exact ordVonNeumann_mem w x this hw
        have hyy : OrdVonNeumann y := by exact ordVonNeumann_mem w y this hwc
        exact ordVonNeumann_mem_or_eq_or_mem x y hxx hyy
      · rw [nonempty_def]
        rw [Ne] at hnX
        rw [eq_empty] at hnX
        push_neg at hnX
        assumption
      · rw [nonempty_def]
        rw [Ne] at hnX
        rw [eq_empty] at hnX
        push_neg at hnX
        assumption
  · intro x hx y hy
    rw [mem_sInter]
    · intro v hv
      have : OrdVonNeumann v := by exact ordVonNeumann_mem X v (hX v hv) hv
      rw [mem_sInter] at hx
      · apply hx at hv
        apply this.2 at hv
        apply hv at hy
        assumption
      · rw [nonempty_def]
        rw [Ne] at hnX
        rw [eq_empty] at hnX
        push_neg at hnX
        assumption
    · rw [nonempty_def]
      rw [Ne] at hnX
      rw [eq_empty] at hnX
      push_neg at hnX
      assumption
}

theorem ord_Trans_iff_VonNeumann (X : ZFSet) : OrdTrans X ↔ OrdVonNeumann X := by {
  by_cases X = ∅
  · constructor
    · intro hX
      rw [h]
      exact empty_ordVonNeumann
    · intro hX
      rw [h]
      exact empty_ordTrans
  · push_neg at h
    constructor
    · intro hX
      constructor
      · constructor
        · intro x hx hnem
          apply regularity at hnem
          obtain ⟨y, hya, hyb⟩ := hnem
          use y
          constructor
          · assumption
          · by_contra h
            obtain ⟨w, hw⟩ := h
            rw [←mem_inter] at hw
            rw [eq_empty] at hyb
            apply hyb w
            assumption
        · intro x hx y hy
          have hxord : OrdTrans x := by exact ordTrans_mem X x hX hx
          have xyord : OrdTrans y := by exact ordTrans_mem X y hX hy
          apply ordTrans_mem_or_eq_or_mem <;> assumption
      · exact hX.1
    · intro hX
      constructor
      · exact hX.2
      · intro x hx
        have : OrdVonNeumann x := by exact ordVonNeumann_mem X x hX hx
        exact this.2
}

def succ' (X : ZFSet) (n : Nat) : ZFSet :=
  Nat.repeat succ n X

def natural (X : ZFSet) : Prop :=
  ∃ n, X = succ' ∅ n

def IsInductive (X : ZFSet) : Prop :=
  ∅ ∈ X ∧ ∀ x ∈ X, succ x ∈ X

axiom infinity : ∃ X, IsInductive X

def mem_all_ind (W : ZFSet) : Prop :=
  ∀ (x : ZFSet), (x ∈ W ↔ ∀ X, (IsInductive X → x ∈ X))

lemma mem_ind_mem_succ (x : ZFSet) : (∀ X, IsInductive X → x ∈ X) → (∀ X, IsInductive X → succ x ∈ X) := by {
  intro h X hX
  apply hX.2
  apply h
  assumption
}

lemma ind_of_mem_all_ind (Z : ZFSet) : mem_all_ind Z → IsInductive Z := by {
  intro hZ
  constructor
  · have h : ∀ X, IsInductive X → ∅ ∈ X := by {
      intro X hX
      exact hX.1
    }
    have : ∅ ∈ Z ↔ ∀ X, IsInductive X → ∅ ∈ X := by exact hZ ∅
    apply this.2 at h
    assumption
  · intro x hx
    rw [mem_all_ind] at hZ
    have : ∀ X, IsInductive X → x ∈ X := by {
      rw [hZ] at hx
      assumption
    }
    have this₀ : ∀ X, IsInductive X → succ x ∈ X := by {
      intro X hX
      apply hX.2
      apply this
      assumption
    }
    rw [hZ]
    assumption
}

theorem mem_all_ind_unique : ∃ W, (mem_all_ind W ∧ (∀ V, mem_all_ind V → V = W)) := by {
  have : ∃ X, IsInductive X := by exact infinity
  obtain ⟨I, hI⟩ := this
  let p := fun x ↦ ∀ Y, IsInductive Y → x ∈ Y
  let W := ZFSet.sep p I
  use W
  constructor
  · rw [mem_all_ind]
    intro x
    constructor
    · intro hx X hX
      rw [mem_sep] at hx
      apply hx.2
      assumption
    · intro h
      rw [mem_sep]
      constructor
      · apply h
        assumption
      · assumption
  · intro V hV
    have : IsInductive V := by exact ind_of_mem_all_ind V hV
    rw [ext_iff]
    intro z
    constructor
    · intro hz
      have this₁ : IsInductive W := by {
        constructor
        · rw [mem_sep]
          constructor
          · exact hI.1
          · intro X hX
            exact hX.1
        · intro x hx
          rw [mem_sep]
          constructor
          · apply hI.2
            rw [mem_sep] at hx
            exact hx.1
          · intro X hX
            rw [mem_sep] at hx
            apply hX.2
            apply hx.2
            assumption
      }
      rw [mem_sep]
      rw [hV] at hz
      constructor
      · apply hz at hI
        assumption
      · exact hz
    · intro hz
      rw [mem_sep] at hz
      apply hz.2
      assumption
}

theorem nat_in_omega (O : ZFSet) (hO : mem_all_ind O) : ∀ (n : Nat), succ' ∅ n ∈ O := by {
  intro n
  induction n with
  | zero => rw [succ']
            rw [Nat.repeat]
            apply ind_of_mem_all_ind at hO
            exact hO.1
  | succ n ih => rw [succ']
                 rw [Nat.repeat]
                 apply ind_of_mem_all_ind at hO
                 rw [IsInductive] at hO
                 apply hO.2
                 exact ih
}
