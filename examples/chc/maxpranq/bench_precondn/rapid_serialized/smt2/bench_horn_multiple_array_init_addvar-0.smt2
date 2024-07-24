; main()
; {
;    i = 1 @l5
;    while (i < alength) @l7
;    {
;       if (i <= j) @l10
;       {
;          a[i] = j @l11
;          i = (i) + (1) @l12
;       }
;       else
;       {
;          skip @l14
;       }
;    }
;    i = 0 @l17
;    while (i < alength) @l18
;    {
;       a[i] = (a[i]) + (i) @l20
;       i = (i) + (1) @l21
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const j Int)
(declare-const l5 Time)
(declare-fun l7 (Nat) Time)
(declare-const nl7 Nat)
(declare-fun l10 (Nat) Time)
(declare-fun l11 (Nat) Time)
(declare-fun l12 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-const l17 Time)
(declare-fun l18 (Nat) Time)
(declare-const nl18 Nat)
(declare-fun l20 (Nat) Time)
(declare-fun l21 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l7 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l7 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l7 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l7 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l7 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l7 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l7 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l7 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l18 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l18 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l7 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l7 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l18 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l18 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l7
      (and
         ;Define variable values at beginning of loop
         (= (i (l7 zero)) 1)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl7 Nat))
            (=>
               (Sub Itl7 nl7)
               (< (i (l7 Itl7)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl7 Nat))
            (=>
               (Sub Itl7 nl7)
               ;Semantics of IfElse at location l10
               (and
                  ;Semantics of left branch
                  (=>
                     (<= (i (l7 Itl7)) j)
                     (and
                        ;Update array variable a at location l11
                        (and
                           (= (a (l12 Itl7) (i (l7 Itl7))) j)
                           (forall ((pos Int))
                              (=>
                                 (not
                                    (= pos (i (l7 Itl7)))
                                 )
                                 (= (a (l12 Itl7) pos) (a (l7 Itl7) pos))
                              )
                           )
                        )
                        (forall ((pos Int))
                           (= (a (l7 (s Itl7)) pos) (a (l12 Itl7) pos))
                        )
                        (= (i (l7 (s Itl7))) (+ (i (l7 Itl7)) 1))
                     )
                  )
                  ;Semantics of right branch
                  (=>
                     (not
                        (<= (i (l7 Itl7)) j)
                     )
                     (and
                        (forall ((pos Int))
                           (= (a (l7 (s Itl7)) pos) (a (l7 Itl7) pos))
                        )
                        (= (i (l7 (s Itl7))) (i (l7 Itl7)))
                     )
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l7 nl7)) alength)
         )
      )
      ;Loop at location l18
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l18 zero)) 0)
            (forall ((pos Int))
               (= (a (l18 zero) pos) (a (l7 nl7) pos))
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl18 Nat))
            (=>
               (Sub Itl18 nl18)
               (< (i (l18 Itl18)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl18 Nat))
            (=>
               (Sub Itl18 nl18)
               (and
                  ;Update array variable a at location l20
                  (and
                     (= (a (l21 Itl18) (i (l18 Itl18))) (+ (a (l18 Itl18) (i (l18 Itl18))) (i (l18 Itl18))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l18 Itl18)))
                           )
                           (= (a (l21 Itl18) pos) (a (l18 Itl18) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l18 (s Itl18))) (+ (i (l18 Itl18)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l18 (s Itl18)) pos) (a (l21 Itl18) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l18 nl18)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l18 nl18)))
         (forall ((pos Int))
            (= (a main_end pos) (a (l18 nl18) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l7 boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (= (i (l7 boundL)) (i (l7 Itl7)))
               )
               (= (i (l7 boundL)) (i (l7 (s Itl7))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l7 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l7 boundL)) (i (l7 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l7 boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (<= (i (l7 boundL)) (i (l7 Itl7)))
               )
               (<= (i (l7 boundL)) (i (l7 (s Itl7))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l7 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l7 boundL)) (i (l7 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l7 boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (>= (i (l7 boundL)) (i (l7 Itl7)))
               )
               (>= (i (l7 boundL)) (i (l7 (s Itl7))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l7 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l7 boundL)) (i (l7 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l7 pos boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (= (a (l7 boundL) pos) (a (l7 Itl7) pos))
               )
               (= (a (l7 boundL) pos) (a (l7 (s Itl7)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l7 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l7 boundL) pos) (a (l7 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l7 pos boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (<= (a (l7 boundL) pos) (a (l7 Itl7) pos))
               )
               (<= (a (l7 boundL) pos) (a (l7 (s Itl7)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l7 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l7 boundL) pos) (a (l7 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l7 pos boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (>= (a (l7 boundL) pos) (a (l7 Itl7) pos))
               )
               (>= (a (l7 boundL) pos) (a (l7 (s Itl7)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l7 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l7 boundL) pos) (a (l7 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (<= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (<= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (>= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (>= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (= (a (l18 boundL) pos) (a (l18 Itl18) pos))
               )
               (= (a (l18 boundL) pos) (a (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l18 boundL) pos) (a (l18 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (<= (a (l18 boundL) pos) (a (l18 Itl18) pos))
               )
               (<= (a (l18 boundL) pos) (a (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l18 boundL) pos) (a (l18 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (>= (a (l18 boundL) pos) (a (l18 Itl18) pos))
               )
               (>= (a (l18 boundL) pos) (a (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l18 boundL) pos) (a (l18 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l7
(assert
   (=
      Dense-i-l7
      (forall ((Itl7 Nat))
         (=>
            (Sub Itl7 nl7)
            (or
               (= (i (l7 (s Itl7))) (i (l7 Itl7)))
               (= (i (l7 (s Itl7))) (+ (i (l7 Itl7)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l7
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l7 xInt)
         (and
            (<= (i (l7 zero)) xInt)
            (< xInt (i (l7 nl7)))
            Dense-i-l7
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l7
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l7 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl7)
               (= (i (l7 it)) xInt)
               (= (i (l7 (s it))) (+ (i (l7 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l18
(assert
   (=
      Dense-i-l18
      (forall ((Itl18 Nat))
         (=>
            (Sub Itl18 nl18)
            (or
               (= (i (l18 (s Itl18))) (i (l18 Itl18)))
               (= (i (l18 (s Itl18))) (+ (i (l18 Itl18)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l18
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l18 xInt)
         (and
            (<= (i (l18 zero)) xInt)
            (< xInt (i (l18 nl18)))
            Dense-i-l18
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l18
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l18 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl18)
               (= (i (l18 it)) xInt)
               (= (i (l18 (s it))) (+ (i (l18 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l7
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l7
            (= (i (l7 (s it1))) (+ (i (l7 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl7))
         )
         (not
            (= (i (l7 it1)) (i (l7 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l18
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l18
            (= (i (l18 (s it1))) (+ (i (l18 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl18))
         )
         (not
            (= (i (l18 it1)) (i (l18 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l7
(assert
   (=>
      (< (i (l7 zero)) alength)
      (exists ((Itl7 Nat))
         (= (s Itl7) nl7)
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l18
(assert
   (=>
      (< (i (l18 zero)) alength)
      (exists ((Itl18 Nat))
         (= (s Itl18) nl18)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (< 0 pos)
            (< pos alength)
            (<= alength (i main_end))
         )
         (<= (* 2 pos) (a main_end pos))
      )
   )
)

(check-sat)

