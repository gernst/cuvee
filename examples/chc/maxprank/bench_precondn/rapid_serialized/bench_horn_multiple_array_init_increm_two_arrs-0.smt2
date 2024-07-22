; main()
; {
;    i = 1 @l6
;    while (i < alength) @l8
;    {
;       if (k <= j) @l12
;       {
;          a[i] = j @l13
;          b[i] = k @l14
;          i = (i) + (1) @l15
;       }
;       else
;       {
;          skip @l17
;       }
;    }
;    i = 0 @l20
;    while (i < alength) @l21
;    {
;       a[i] = (a[i]) + (1) @l23
;       b[i] = (b[i]) + (1) @l24
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
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const j Int)
(declare-const k Int)
(declare-const l6 Time)
(declare-fun l8 (Nat) Time)
(declare-const nl8 Nat)
(declare-fun l12 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-fun l17 (Nat) Time)
(declare-const l20 Time)
(declare-fun l21 (Nat) Time)
(declare-const nl21 Nat)
(declare-fun l23 (Nat) Time)
(declare-fun l24 (Nat) Time)
(declare-fun l25 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l21 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l21 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l21 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l21 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l8
      (and
         ;Define variable values at beginning of loop
         (= (i (l8 zero)) 1)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               (< (i (l8 Itl8)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               ;Semantics of IfElse at location l12
               (and
                  ;Semantics of left branch
                  (=>
                     (<= k j)
                     (and
                        ;Update array variable a at location l13
                        (and
                           (= (a (l14 Itl8) (i (l8 Itl8))) j)
                           (forall ((pos Int))
                              (=>
                                 (not
                                    (= pos (i (l8 Itl8)))
                                 )
                                 (= (a (l14 Itl8) pos) (a (l8 Itl8) pos))
                              )
                           )
                        )
                        ;Update array variable b at location l14
                        (and
                           (= (b (l15 Itl8) (i (l8 Itl8))) k)
                           (forall ((pos Int))
                              (=>
                                 (not
                                    (= pos (i (l8 Itl8)))
                                 )
                                 (= (b (l15 Itl8) pos) (b (l8 Itl8) pos))
                              )
                           )
                        )
                        (forall ((pos Int))
                           (= (a (l8 (s Itl8)) pos) (a (l14 Itl8) pos))
                        )
                        (forall ((pos Int))
                           (= (b (l8 (s Itl8)) pos) (b (l15 Itl8) pos))
                        )
                        (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
                     )
                  )
                  ;Semantics of right branch
                  (=>
                     (not
                        (<= k j)
                     )
                     (and
                        (forall ((pos Int))
                           (= (a (l8 (s Itl8)) pos) (a (l8 Itl8) pos))
                        )
                        (forall ((pos Int))
                           (= (b (l8 (s Itl8)) pos) (b (l8 Itl8) pos))
                        )
                        (= (i (l8 (s Itl8))) (i (l8 Itl8)))
                     )
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l8 nl8)) alength)
         )
      )
      ;Loop at location l21
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l21 zero)) 0)
            (forall ((pos Int))
               (= (b (l21 zero) pos) (b (l8 nl8) pos))
            )
            (forall ((pos Int))
               (= (a (l21 zero) pos) (a (l8 nl8) pos))
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl21 Nat))
            (=>
               (Sub Itl21 nl21)
               (< (i (l21 Itl21)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl21 Nat))
            (=>
               (Sub Itl21 nl21)
               (and
                  ;Update array variable a at location l23
                  (and
                     (= (a (l24 Itl21) (i (l21 Itl21))) (+ (a (l21 Itl21) (i (l21 Itl21))) 1))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l21 Itl21)))
                           )
                           (= (a (l24 Itl21) pos) (a (l21 Itl21) pos))
                        )
                     )
                  )
                  ;Update array variable b at location l24
                  (and
                     (= (b (l25 Itl21) (i (l21 Itl21))) (+ (b (l21 Itl21) (i (l21 Itl21))) 1))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l21 Itl21)))
                           )
                           (= (b (l25 Itl21) pos) (b (l21 Itl21) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l21 (s Itl21))) (+ (i (l21 Itl21)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l21 (s Itl21)) pos) (b (l25 Itl21) pos))
                  )
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l21 (s Itl21)) pos) (a (l24 Itl21) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l21 nl21)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l21 nl21)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l21 nl21) pos))
         )
         (forall ((pos Int))
            (= (a main_end pos) (a (l21 nl21) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (<= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (>= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (b (l8 boundL) pos) (b (l8 Itl8) pos))
               )
               (= (b (l8 boundL) pos) (b (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l8 boundL) pos) (b (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (b (l8 boundL) pos) (b (l8 Itl8) pos))
               )
               (<= (b (l8 boundL) pos) (b (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l8 boundL) pos) (b (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (b (l8 boundL) pos) (b (l8 Itl8) pos))
               )
               (>= (b (l8 boundL) pos) (b (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l8 boundL) pos) (b (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (<= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (>= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (<= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (>= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (<= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (>= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (a (l21 boundL) pos) (a (l21 Itl21) pos))
               )
               (= (a (l21 boundL) pos) (a (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l21 boundL) pos) (a (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (a (l21 boundL) pos) (a (l21 Itl21) pos))
               )
               (<= (a (l21 boundL) pos) (a (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l21 boundL) pos) (a (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (a (l21 boundL) pos) (a (l21 Itl21) pos))
               )
               (>= (a (l21 boundL) pos) (a (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l21 boundL) pos) (a (l21 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l8
(assert
   (=
      Dense-i-l8
      (forall ((Itl8 Nat))
         (=>
            (Sub Itl8 nl8)
            (or
               (= (i (l8 (s Itl8))) (i (l8 Itl8)))
               (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l8
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l8 xInt)
         (and
            (<= (i (l8 zero)) xInt)
            (< xInt (i (l8 nl8)))
            Dense-i-l8
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l8
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l8 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl8)
               (= (i (l8 it)) xInt)
               (= (i (l8 (s it))) (+ (i (l8 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l21
(assert
   (=
      Dense-i-l21
      (forall ((Itl21 Nat))
         (=>
            (Sub Itl21 nl21)
            (or
               (= (i (l21 (s Itl21))) (i (l21 Itl21)))
               (= (i (l21 (s Itl21))) (+ (i (l21 Itl21)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l21
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l21 xInt)
         (and
            (<= (i (l21 zero)) xInt)
            (< xInt (i (l21 nl21)))
            Dense-i-l21
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l21
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l21 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl21)
               (= (i (l21 it)) xInt)
               (= (i (l21 (s it))) (+ (i (l21 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l8
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l8
            (= (i (l8 (s it1))) (+ (i (l8 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl8))
         )
         (not
            (= (i (l8 it1)) (i (l8 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l21
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l21
            (= (i (l21 (s it1))) (+ (i (l21 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl21))
         )
         (not
            (= (i (l21 it1)) (i (l21 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l8
(assert
   (=>
      (< (i (l8 zero)) alength)
      (exists ((Itl8 Nat))
         (= (s Itl8) nl8)
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l21
(assert
   (=>
      (< (i (l21 zero)) alength)
      (exists ((Itl21 Nat))
         (= (s Itl21) nl21)
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
         (<= (b main_end pos) (a main_end pos))
      )
   )
)

(check-sat)

