; main()
; {
;    i = 1 @l5
;    while (i < alength) @l7
;    {
;       if (0 <= j) @l10
;       {
;          a[i] = j @l11
;          i = (i) + (1) @l12
;       }
;       else
;       {
;          skip @l14
;       }
;    }
;    i = 0 @l18
;    while (i < alength) @l19
;    {
;       a[i] = (a[i]) + (1) @l21
;       i = (i) + (1) @l22
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
(declare-const l18 Time)
(declare-fun l19 (Nat) Time)
(declare-const nl19 Nat)
(declare-fun l21 (Nat) Time)
(declare-fun l22 (Nat) Time)
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
(declare-lemma-predicate BC-AxEvol-eq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l7 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l7 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l19 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l19 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l7 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l7 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l19 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l19 (Nat Nat Nat) Bool)

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
                     (<= 0 j)
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
                        (<= 0 j)
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
      ;Loop at location l19
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l19 zero)) 0)
            (forall ((pos Int))
               (= (a (l19 zero) pos) (a (l7 nl7) pos))
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl19 Nat))
            (=>
               (Sub Itl19 nl19)
               (< (i (l19 Itl19)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl19 Nat))
            (=>
               (Sub Itl19 nl19)
               (and
                  ;Update array variable a at location l21
                  (and
                     (= (a (l22 Itl19) (i (l19 Itl19))) (+ (a (l19 Itl19) (i (l19 Itl19))) 1))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l19 Itl19)))
                           )
                           (= (a (l22 Itl19) pos) (a (l19 Itl19) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l19 (s Itl19))) (+ (i (l19 Itl19)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l19 (s Itl19)) pos) (a (l22 Itl19) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l19 nl19)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l19 nl19)))
         (forall ((pos Int))
            (= (a main_end pos) (a (l19 nl19) pos))
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

; Definition: Premise for value-evolution-eq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (<= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (>= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (a (l19 boundL) pos) (a (l19 Itl19) pos))
               )
               (= (a (l19 boundL) pos) (a (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l19 boundL) pos) (a (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (a (l19 boundL) pos) (a (l19 Itl19) pos))
               )
               (<= (a (l19 boundL) pos) (a (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l19 boundL) pos) (a (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (a (l19 boundL) pos) (a (l19 Itl19) pos))
               )
               (>= (a (l19 boundL) pos) (a (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l19 boundL) pos) (a (l19 boundR) pos))
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

; Definition: Dense for i-l19
(assert
   (=
      Dense-i-l19
      (forall ((Itl19 Nat))
         (=>
            (Sub Itl19 nl19)
            (or
               (= (i (l19 (s Itl19))) (i (l19 Itl19)))
               (= (i (l19 (s Itl19))) (+ (i (l19 Itl19)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l19
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l19 xInt)
         (and
            (<= (i (l19 zero)) xInt)
            (< xInt (i (l19 nl19)))
            Dense-i-l19
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l19
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l19 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl19)
               (= (i (l19 it)) xInt)
               (= (i (l19 (s it))) (+ (i (l19 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-i-l19
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l19
            (= (i (l19 (s it1))) (+ (i (l19 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl19))
         )
         (not
            (= (i (l19 it1)) (i (l19 it2)))
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

; Axiom: already-proven-lemma atLeastOneIteration-l19
(assert
   (=>
      (< (i (l19 zero)) alength)
      (exists ((Itl19 Nat))
         (= (s Itl19) nl19)
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
         (<= 1 (a main_end pos))
      )
   )
)

(check-sat)

