; main()
; {
;    i = 0 @l7
;    while (i < alength) @l9
;    {
;       if (3 <= (j) + (k)) @l13
;       {
;          a[i] = j @l14
;          b[i] = k @l15
;          i = (i) + (1) @l16
;       }
;       else
;       {
;          skip @l18
;       }
;    }
;    i = 0 @l22
;    while (i < alength) @l23
;    {
;       c[i] = (a[i]) + (b[i]) @l25
;       i = (i) + (1) @l26
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
(declare-const j Int)
(declare-const k Int)
(declare-const l7 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-fun l16 (Nat) Time)
(declare-fun l18 (Nat) Time)
(declare-const l22 Time)
(declare-fun l23 (Nat) Time)
(declare-const nl23 Nat)
(declare-fun l25 (Nat) Time)
(declare-fun l26 (Nat) Time)
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
(declare-lemma-predicate BC-AxEvol-eq-i-l23 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l23 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l23 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l23 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l23 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l23 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l23 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l23 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l23 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l23 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l23 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l23 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l23 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l23 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l23 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l23 (Nat Nat Nat) Bool)

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
                     (<= 3 (+ j k))
                     (and
                        ;Update array variable a at location l14
                        (and
                           (= (a (l15 Itl9) (i (l9 Itl9))) j)
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
                           (= (b (l16 Itl9) (i (l9 Itl9))) k)
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
                        (<= 3 (+ j k))
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
      ;Loop at location l23
      (and
         ;Define variable values at beginning of loop
         (= (i (l23 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl23 Nat))
            (=>
               (Sub Itl23 nl23)
               (< (i (l23 Itl23)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl23 Nat))
            (=>
               (Sub Itl23 nl23)
               (and
                  ;Update array variable c at location l25
                  (and
                     (= (c (l26 Itl23) (i (l23 Itl23))) (+ (a (l9 nl9) (i (l23 Itl23))) (b (l9 nl9) (i (l23 Itl23)))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l23 Itl23)))
                           )
                           (= (c (l26 Itl23) pos) (c (l23 Itl23) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l23 (s Itl23))) (+ (i (l23 Itl23)) 1))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l23 (s Itl23)) pos) (c (l26 Itl23) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l23 nl23)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l23 nl23)))
         (forall ((pos Int))
            (= (c main_end pos) (c (l23 nl23) pos))
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

; Definition: Premise for value-evolution-eq-i-l23
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l23 boundL boundR)
         (forall ((Itl23 Nat))
            (=>
               (and
                  (Sub boundL (s Itl23))
                  (Sub Itl23 boundR)
                  (= (i (l23 boundL)) (i (l23 Itl23)))
               )
               (= (i (l23 boundL)) (i (l23 (s Itl23))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l23
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l23 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l23 boundL)) (i (l23 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l23
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l23 boundL boundR)
         (forall ((Itl23 Nat))
            (=>
               (and
                  (Sub boundL (s Itl23))
                  (Sub Itl23 boundR)
                  (<= (i (l23 boundL)) (i (l23 Itl23)))
               )
               (<= (i (l23 boundL)) (i (l23 (s Itl23))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l23
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l23 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l23 boundL)) (i (l23 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l23
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l23 boundL boundR)
         (forall ((Itl23 Nat))
            (=>
               (and
                  (Sub boundL (s Itl23))
                  (Sub Itl23 boundR)
                  (>= (i (l23 boundL)) (i (l23 Itl23)))
               )
               (>= (i (l23 boundL)) (i (l23 (s Itl23))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l23
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l23 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l23 boundL)) (i (l23 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l23
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l23 pos boundL boundR)
         (forall ((Itl23 Nat))
            (=>
               (and
                  (Sub boundL (s Itl23))
                  (Sub Itl23 boundR)
                  (= (c (l23 boundL) pos) (c (l23 Itl23) pos))
               )
               (= (c (l23 boundL) pos) (c (l23 (s Itl23)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l23
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l23 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l23 boundL) pos) (c (l23 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l23
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l23 pos boundL boundR)
         (forall ((Itl23 Nat))
            (=>
               (and
                  (Sub boundL (s Itl23))
                  (Sub Itl23 boundR)
                  (<= (c (l23 boundL) pos) (c (l23 Itl23) pos))
               )
               (<= (c (l23 boundL) pos) (c (l23 (s Itl23)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l23
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l23 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l23 boundL) pos) (c (l23 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l23
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l23 pos boundL boundR)
         (forall ((Itl23 Nat))
            (=>
               (and
                  (Sub boundL (s Itl23))
                  (Sub Itl23 boundR)
                  (>= (c (l23 boundL) pos) (c (l23 Itl23) pos))
               )
               (>= (c (l23 boundL) pos) (c (l23 (s Itl23)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l23
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l23 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l23 boundL) pos) (c (l23 boundR) pos))
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

; Definition: Dense for i-l23
(assert
   (=
      Dense-i-l23
      (forall ((Itl23 Nat))
         (=>
            (Sub Itl23 nl23)
            (or
               (= (i (l23 (s Itl23))) (i (l23 Itl23)))
               (= (i (l23 (s Itl23))) (+ (i (l23 Itl23)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l23
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l23 xInt)
         (and
            (<= (i (l23 zero)) xInt)
            (< xInt (i (l23 nl23)))
            Dense-i-l23
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l23
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l23 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl23)
               (= (i (l23 it)) xInt)
               (= (i (l23 (s it))) (+ (i (l23 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-i-l23
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l23
            (= (i (l23 (s it1))) (+ (i (l23 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl23))
         )
         (not
            (= (i (l23 it1)) (i (l23 it2)))
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

; Axiom: already-proven-lemma atLeastOneIteration-l23
(assert
   (=>
      (< (i (l23 zero)) alength)
      (exists ((Itl23 Nat))
         (= (s Itl23) nl23)
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
         (<= 3 (c main_end pos))
      )
   )
)

(check-sat)

