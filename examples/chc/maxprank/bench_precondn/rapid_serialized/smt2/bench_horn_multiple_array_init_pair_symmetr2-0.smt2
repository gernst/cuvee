; main()
; {
;    i = 0 @l7
;    while (i < alength) @l9
;    {
;       if (x > y) @l13
;       {
;          a[i] = x @l14
;          b[i] = y @l15
;          i = (i) + (1) @l16
;       }
;       else
;       {
;          skip @l18
;       }
;    }
;    i = 0 @l21
;    while (i < alength) @l22
;    {
;       c[i] = (a[i]) - (b[i]) @l24
;       i = (i) + (1) @l25
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-fun b (Time Int) Int)
(declare-fun c (Time Int) Int)
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const l7 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-fun l16 (Nat) Time)
(declare-fun l18 (Nat) Time)
(declare-const l21 Time)
(declare-fun l22 (Nat) Time)
(declare-const nl22 Nat)
(declare-fun l24 (Nat) Time)
(declare-fun l25 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l22 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l22 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l22 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l22 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l22 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l22 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l22 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l22 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l22 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l22 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l22 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l22 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l22 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l22 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l22 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l22 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l9
      (and
         ;Define variable values at beginning of loop
         (= (i (l9 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (< (i (l9 Itl9)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               ;Semantics of IfElse at location l13
               (and
                  ;Semantics of left branch
                  (=>
                     (> x y)
                     (and
                        ;Update array variable a at location l14
                        (and
                           (= (a (l15 Itl9) (i (l9 Itl9))) x)
                           (forall ((pos Int))
                              (=>
                                 (not
                                    (= pos (i (l9 Itl9)))
                                 )
                                 (= (a (l15 Itl9) pos) (a (l9 Itl9) pos))
                              )
                           )
                        )
                        ;Update array variable b at location l15
                        (and
                           (= (b (l16 Itl9) (i (l9 Itl9))) y)
                           (forall ((pos Int))
                              (=>
                                 (not
                                    (= pos (i (l9 Itl9)))
                                 )
                                 (= (b (l16 Itl9) pos) (b (l9 Itl9) pos))
                              )
                           )
                        )
                        (forall ((pos Int))
                           (= (a (l9 (s Itl9)) pos) (a (l15 Itl9) pos))
                        )
                        (forall ((pos Int))
                           (= (b (l9 (s Itl9)) pos) (b (l16 Itl9) pos))
                        )
                        (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
                     )
                  )
                  ;Semantics of right branch
                  (=>
                     (not
                        (> x y)
                     )
                     (and
                        (forall ((pos Int))
                           (= (a (l9 (s Itl9)) pos) (a (l9 Itl9) pos))
                        )
                        (forall ((pos Int))
                           (= (b (l9 (s Itl9)) pos) (b (l9 Itl9) pos))
                        )
                        (= (i (l9 (s Itl9))) (i (l9 Itl9)))
                     )
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l9 nl9)) alength)
         )
      )
      ;Loop at location l22
      (and
         ;Define variable values at beginning of loop
         (= (i (l22 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl22 Nat))
            (=>
               (Sub Itl22 nl22)
               (< (i (l22 Itl22)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl22 Nat))
            (=>
               (Sub Itl22 nl22)
               (and
                  ;Update array variable c at location l24
                  (and
                     (= (c (l25 Itl22) (i (l22 Itl22))) (- (a (l9 nl9) (i (l22 Itl22))) (b (l9 nl9) (i (l22 Itl22)))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l22 Itl22)))
                           )
                           (= (c (l25 Itl22) pos) (c (l22 Itl22) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l22 (s Itl22))) (+ (i (l22 Itl22)) 1))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l22 (s Itl22)) pos) (c (l25 Itl22) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l22 nl22)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l22 nl22)))
         (forall ((pos Int))
            (= (c main_end pos) (c (l22 nl22) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (<= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (>= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (<= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (>= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (<= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (>= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l22
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l22 boundL boundR)
         (forall ((Itl22 Nat))
            (=>
               (and
                  (Sub boundL (s Itl22))
                  (Sub Itl22 boundR)
                  (= (i (l22 boundL)) (i (l22 Itl22)))
               )
               (= (i (l22 boundL)) (i (l22 (s Itl22))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l22
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l22 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l22 boundL)) (i (l22 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l22
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l22 boundL boundR)
         (forall ((Itl22 Nat))
            (=>
               (and
                  (Sub boundL (s Itl22))
                  (Sub Itl22 boundR)
                  (<= (i (l22 boundL)) (i (l22 Itl22)))
               )
               (<= (i (l22 boundL)) (i (l22 (s Itl22))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l22
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l22 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l22 boundL)) (i (l22 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l22
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l22 boundL boundR)
         (forall ((Itl22 Nat))
            (=>
               (and
                  (Sub boundL (s Itl22))
                  (Sub Itl22 boundR)
                  (>= (i (l22 boundL)) (i (l22 Itl22)))
               )
               (>= (i (l22 boundL)) (i (l22 (s Itl22))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l22
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l22 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l22 boundL)) (i (l22 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l22
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l22 pos boundL boundR)
         (forall ((Itl22 Nat))
            (=>
               (and
                  (Sub boundL (s Itl22))
                  (Sub Itl22 boundR)
                  (= (c (l22 boundL) pos) (c (l22 Itl22) pos))
               )
               (= (c (l22 boundL) pos) (c (l22 (s Itl22)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l22
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l22 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l22 boundL) pos) (c (l22 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l22
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l22 pos boundL boundR)
         (forall ((Itl22 Nat))
            (=>
               (and
                  (Sub boundL (s Itl22))
                  (Sub Itl22 boundR)
                  (<= (c (l22 boundL) pos) (c (l22 Itl22) pos))
               )
               (<= (c (l22 boundL) pos) (c (l22 (s Itl22)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l22
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l22 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l22 boundL) pos) (c (l22 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l22
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l22 pos boundL boundR)
         (forall ((Itl22 Nat))
            (=>
               (and
                  (Sub boundL (s Itl22))
                  (Sub Itl22 boundR)
                  (>= (c (l22 boundL) pos) (c (l22 Itl22) pos))
               )
               (>= (c (l22 boundL) pos) (c (l22 (s Itl22)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l22
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l22 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l22 boundL) pos) (c (l22 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l9
(assert
   (=
      Dense-i-l9
      (forall ((Itl9 Nat))
         (=>
            (Sub Itl9 nl9)
            (or
               (= (i (l9 (s Itl9))) (i (l9 Itl9)))
               (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l9 xInt)
         (and
            (<= (i (l9 zero)) xInt)
            (< xInt (i (l9 nl9)))
            Dense-i-l9
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l9 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl9)
               (= (i (l9 it)) xInt)
               (= (i (l9 (s it))) (+ (i (l9 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l22
(assert
   (=
      Dense-i-l22
      (forall ((Itl22 Nat))
         (=>
            (Sub Itl22 nl22)
            (or
               (= (i (l22 (s Itl22))) (i (l22 Itl22)))
               (= (i (l22 (s Itl22))) (+ (i (l22 Itl22)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l22
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l22 xInt)
         (and
            (<= (i (l22 zero)) xInt)
            (< xInt (i (l22 nl22)))
            Dense-i-l22
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l22
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l22 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl22)
               (= (i (l22 it)) xInt)
               (= (i (l22 (s it))) (+ (i (l22 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l9
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l9
            (= (i (l9 (s it1))) (+ (i (l9 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl9))
         )
         (not
            (= (i (l9 it1)) (i (l9 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l22
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l22
            (= (i (l22 (s it1))) (+ (i (l22 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl22))
         )
         (not
            (= (i (l22 it1)) (i (l22 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l9
(assert
   (=>
      (< (i (l9 zero)) alength)
      (exists ((Itl9 Nat))
         (= (s Itl9) nl9)
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l22
(assert
   (=>
      (< (i (l22 zero)) alength)
      (exists ((Itl22 Nat))
         (= (s Itl22) nl22)
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
         (< 0 (c main_end pos))
      )
   )
)

(check-sat)

