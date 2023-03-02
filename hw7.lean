namespace HW7

/-
Your task in this HW is to replace all instances of `sorry` with proofs without errors. If you aren't able to complete a proof, get as much done as you can, and leave `sorry` in the cases you cannot finish. Partial work is better than nothing!

For this assignment, we redefine the inductive types we will use, and the operations on them, in order to not have standard library automation & already proved theorems get in the way of the assignment. Later on, we will _use_ this automation, but for now, it will get in the way of learning how to prove theorems.

NOTE: For this HW, you cannot use the special List syntax: you must use List.nil & List.cons. You _can_ use number literals (0,1,2, etc) for Nat. 
-/

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

def natOfNat : _root_.Nat -> Nat
| _root_.Nat.zero => Nat.zero
| _root_.Nat.succ n => Nat.succ (natOfNat n)
-- N.B.: this is the magic that allows us to write numerals
-- instead of Nat.succ (Nat.succ ...). 
instance (n : _root_.Nat) : OfNat Nat n where
  ofNat := natOfNat n

def Nat.sub : Nat → Nat → Nat
  | a, 0      => a
  | 0, _      => 0 
  | Nat.succ a, Nat.succ b => Nat.sub a b

def Nat.add : Nat → Nat → Nat
  | Nat.zero, b   => b
  | Nat.succ a, b => Nat.succ (Nat.add a b)

def Nat.mul : Nat → Nat → Nat
  | _, 0          => 0
  | a, Nat.succ b => Nat.add (Nat.mul a b) a

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

def List.append : List α → List α → List α
  | List.nil,       bs => bs
  | List.cons a as, bs => List.cons a (List.append as bs)

def List.length : List α → Nat
  | List.nil       => 0
  | List.cons _ as => Nat.add (List.length as) 1

def List.reverse : List Nat -> List Nat 
  | List.nil => List.nil
  | List.cons a L => List.append (List.reverse L) (List.cons a List.nil) 

def List.filter (p : α → Bool) : List α → List α
  | List.nil => List.nil
  | List.cons a as => match p a with
    | true => List.cons a (filter p as)
    | false => filter p as

/- BEGIN PROOFS -/

-- First, redo proofs that you did in HW5, but this time, using tactics. 
-- Note that `variable`s do not need to be introduced!

-- part p1
variable (P Q R S : Prop)

theorem t1 : P -> P := 
 by intros p
    exact p

theorem t2 : P -> Q -> P := 
 by intros p _
    exact p

theorem t3 : (P -> Q) -> (Q -> R) -> P -> R := 
 by intros pq qr p
    exact qr (pq p)

theorem t4 : P -> Q -> (Q -> P -> R) -> R := 
 by intros p q qpr 
    exact qpr q p

theorem t5 : (P -> Q) -> (P -> R) -> (R -> Q -> S) -> P -> S := 
 by intros pq pr rqs p
    exact rqs (pr p) (pq p)

theorem t6 : (P -> Q -> R) -> (P -> Q) -> P -> R := 
 by intros pqr pq p
    exact pqr p (pq p)


theorem p3 : P ∧ Q -> (Q -> R) -> R ∧ P := 
 by intros pq qr
    cases pq
    constructor
      case intro.left => exact qr ‹Q›
      case intro.right => exact ‹P›
      


theorem p4 : P ∨ Q -> (P -> R) -> (Q -> R) -> R := 
 by intros pq pr qr
    cases pq
    case inl => exact pr ‹P›
    case inr => exact qr ‹Q›
  

theorem p5 : P ∨ Q -> (P -> R) -> R ∨ Q := 
 by intro porq pr
    cases porq
    apply Or.inl 
    case inl.h => exact pr ‹P›
    apply Or.inr
    case inr.h => exact ‹Q›
      
    

theorem p6 : ¬ Q -> (R -> Q) -> (R ∨ ¬ S) -> S -> False := 
 by intros nq rq rons S
    cases rons
    case inl => exact nq (rq ‹R›)
    case inr h => exact h S

-- part p1

-- Now, some new proofs

-- part p2
theorem and_distrib_or: ∀ A B C : Prop, 
  A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := 
  by intros A B C
     constructor
     case mp => intro aboc
                cases aboc
                cases ‹B ∨ C›
                apply Or.inl
                case intro.inl.h => exact And.intro ‹A› ‹B›
                apply Or.inr
                case intro.inr.h => exact And.intro ‹A› ‹C›
     case mpr => intro g
                 constructor
                    case left => cases g
                                 case inl => cases ‹A ∧ B›
                                             exact ‹A›
                                 case inr => cases ‹A ∧ C›
                                             exact ‹A›
                    case right => cases g 
                                  apply Or.inl 
                                  case inl => cases ‹A ∧ B›
                                              exact ‹B›
                                  apply Or.inr 
                                  case inr => cases ‹A ∧ C›
                                              exact ‹C›

                  
                  
                

                

theorem or_distrib_and: ∀ A B C : Prop, 
  A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) :=
   by intros A B C
      constructor
      case mp => intro g
                 constructor 
                    case left => cases g
                                 apply Or.inl
                                 case inl.h => exact ‹A›
                                 apply Or.inr
                                 case inr.h => cases ‹B ∧ C›
                                               exact ‹B›
                    case right => cases g
                                  apply Or.inl
                                  case inl.h => exact ‹A›
                                  apply Or.inr
                                  case inr.h => cases ‹B ∧ C›
                                                exact ‹C›    
      case mpr => intro g
                  cases g
                  cases ‹A ∨ B›
                  cases ‹A ∨ C› 
                  case intro.inl.inl => apply Or.inl
                                        exact ‹A›
                  case intro.inl.inr => apply Or.inl 
                                        exact ‹A›
                  case intro.inr => cases ‹A ∨ C›
                                    case inl => apply Or.inl
                                                exact ‹A›
                                    case inr => apply Or.inr 
                                                exact And.intro ‹B› ‹C›



                  

                    
                  


-- part p2

-- Now, some proofs that will (likely) require induction, on 
-- either Nat(ural number)s or Lists.

-- part p3
def addtail (n m : Nat) : Nat :=
  match n, m with
  | Nat.zero, m => m
  | Nat.succ n', m => addtail n' (Nat.succ m)

-- 8 lines
theorem addtail_succ : forall n m, 
  Nat.succ (addtail n m) = addtail (Nat.succ n) m :=
 by intros n 
    simp only [addtail]
    induction n
    case zero => intros m
                 rfl
    case succ n h => intros m
                     simp only [addtail]
                     rw [h] 

          

-- 10 lines
theorem add_eq : forall n m, Nat.add n m = addtail n m := 
 by intros n
    induction n
    case zero => intros m
                 rfl
    case succ n h => intros m
                     simp only [Nat.add]
                     rw [h]
                     apply addtail_succ
                     
                     
                          
                                      
                    
-- 9 lines
theorem app_associative: ∀ L1 L2 L3 : List Nat, 
    List.append L1 (List.append L2 L3) = 
    List.append (List.append L1 L2) L3 := 
 by intros l1 
    induction l1
    case nil => intros l2 l3 
                rfl
    case cons h t hp => intros l2 l3 
                        simp only [List.append]
                        rw [hp]
                        

-- 7 lines
theorem minus_x_x: ∀ x : Nat, Nat.sub x x = 0
:= 
 by intros x
    induction x
    case zero => rfl
    case succ n h => simp only [Nat.sub]
                     assumption

-- 5 lines
theorem add_n_1 : ∀ x : Nat, Nat.add x 1 = Nat.succ x :=
 by intros x
    induction x
    case zero => rfl
    case succ x h => simp only [Nat.add]
                     rw [h]



-- 9 lines
theorem mult_1_x: ∀ x : Nat, Nat.mul 1 x = x := 
 by intros x
    induction x
    case zero => rfl
    case succ x h => simp only [Nat.mul]
                     rw [h]
                     apply add_n_1

-- 7 lines
theorem add_assoc: ∀ x y z : Nat, 
  Nat.add x (Nat.add y z) = Nat.add (Nat.add x y) z := 
 by intros x y z
    revert y z
    induction x
    case zero => intros y z 
                 rfl
    case succ x h => intros y z
                     simp only [Nat.add]
                     rw [<- h]
                     

-- 6 lines
theorem add_x_Sy : forall x y, 
  Nat.add x (Nat.succ y) = Nat.succ (Nat.add x y) :=
 by intros x 
    induction x
    case zero => intros y
                 rfl
    case succ x h => intros y
                     simp only [Nat.add]
                     rw [h]

-- 4 lines
theorem add_n_0 : forall n, Nat.add n Nat.zero = n :=
 by intros n 
    induction n
    case zero => rfl
    case succ n h => simp only [Nat.add]
                     rw [h]

-- 13 lines
theorem mult_2_x: ∀ x : Nat, Nat.mul 2 x = Nat.add x x := 
 by intros x
    induction x
    case zero => rfl
    case succ n h => simp only [Nat.mul]
                     rw [h]
                     simp only [Nat.add]
                     rw [<- add_n_1]
                     rw [add_x_Sy]
                     rw [<- add_n_1]
                     rw [<- add_assoc]
                     rw [<- add_assoc]
                     have r: Nat.add 1 1 = 2 := by rfl
                     rw [r]
                     rw [add_assoc]
                     
                     
                     

                     
-- 10 lines
theorem length_append : forall (T : Type) (L1 L2 : List T), 
  List.length (List.append L1 L2) = Nat.add (List.length L1) (List.length L2) :=
 by intros T l1
    induction l1
    case nil => intros l2
                rfl
    case cons head l1 h => intros l2
                           simp only [List.length]
                           rw [h]
                           rw [add_n_1]
                           rw [add_n_1]
                           rfl
                           
                           
                           
                                           
                           


-- 8 lines
theorem rev_length: ∀ L : List Nat, 
  List.length (List.reverse L) = List.length L := 
 by intros l
    induction l
    case nil => rfl
    case cons h tail hp => simp only [List.length]
                           simp only [List.reverse]
                           rw [<- hp]
                           rw [length_append]
                           rfl
                           


-- Consider the following pair of definitions
def even : Nat -> Bool 
| 0 => true
| 1 => false
| Nat.succ (Nat.succ n) => even n

def double : Nat → Nat 
    | 0 => 0
    | (Nat.succ x) => Nat.succ (Nat.succ (double x))

-- 5 lines
theorem even_double: ∀ x : Nat, even (double x) = true := 
 by intros x
    induction x
    case zero => rfl
    case succ n h =>  simp only [even]
                      assumption

                  

-- part p3
end HW7