;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-advanced-reader.ss" "lang")((modname ta-solver-starter) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
;; ta-solver-starter.rkt

; PROBLEM 1:
; 
; Consider a social network similar to Twitter called Chirper. Each user has a name, a note about
; whether or not they are a verified user, and follows some number of people. 
; 
; Design a data definition for Chirper, including a template that is tail recursive and avoids 
; cycles. 
; 
; Then design a function called most-followers which determines which user in a Chirper Network is 
; followed by the most people.
 
;; Data Definitions

(define-struct chirper (name verified follows))
;; Chirper is a (make-chirper String Boolean (listof Chirper))
;; interp. information about a chirper with their name, their verification, and list of chirpers they follow

(define C1 (make-chirper "A" false empty))
(define C2 (make-chirper "A" true (list (make-chirper "B" true empty))))
(define C3 (shared ((-A- (make-chirper "A" false (list -B- -C- -D-)))
                    (-B- (make-chirper "B" true (list -C- -A-)))
                    (-C- (make-chirper "C" false (list -D-)))
                    (-D- (make-chirper "D" true (list -C- -A-))))
             -A-))
(define C4 (shared ((-A- (make-chirper "A" false (list -B- -C- -D-)))
                    (-B- (make-chirper "B" true (list -A-)))
                    (-C- (make-chirper "C" false (list -A-)))
                    (-D- (make-chirper "D" true (list -A-))))
             -A-))

;; template is:
;; tail recursive
;; encapsulated in local
;; structural recursion in fn-for-LOC
;; context preserving acc. what chirpers we have already processed

#;
(define (fn-for-chirper c0)
  ;; todo is a (listof Chirper) a worklist acc.
  ;; visited is a (listof String), context preserving acc. with list of names of chirpers already visited
  (local [(define (fn-for-chirper c todo visited)
            (if (member (chirper-name c) visited)
                (fn-for-loc todo visited)
                (fn-for-loc
                 (append (chirper-follows c) todo)
                 (cons (chirper-name c) visited))))
          (define (fn-for loc todo visited)
            (cond [(empty? todo) (...)]
                  [else (fn-for-chirper (first todo)
                                        (rest todo)
                                        (visited))]))]
    (fn-for-chirper c0 empty empty)))


;; Functions

;; Chirper -> Chirper
;; produce the chirper who has the most followers
(check-expect (most-followers C2) (first (chirper-follows C2)))
(check-expect (most-followers C3) (shared ((-A- (make-chirper "A" false (list -B- -C- -D-)))
                                           (-B- (make-chirper "B" true (list -C- -A-)))
                                           (-C- (make-chirper "C" false (list -D-)))
                                           (-D- (make-chirper "D" true (list -C- -A-))))
                                    -C-))
(check-expect (most-followers C4) C4)

; (define (most-followers c) empty) ;stub
(define (most-followers c0)
  ;; todo is a (listof Chirper) a worklist acc.
  ;; visited is a (listof String), context preserving acc. with list of names of chirpers already visited
  ;; rsf is a (listof ChirperNFollowers); the number of followers each chirper has
  (local [;; ChirperNFollowers is a (make-cnf chirper natural)
          ;; interp. number of followers recorded for a given chirper
          (define-struct cnf (chirper n))
          (define (fn-for-chirper c todo visited rsf)
            (if (member (chirper-name c) visited)
                (fn-for-loc todo visited rsf)
                (fn-for-loc
                 (append (chirper-follows c) todo)
                 (cons (chirper-name c) visited)
                 (merge-chirpers (chirper-follows c) rsf))))
          (define (fn-for-loc todo visited rsf)
            (cond [(empty? todo) rsf]
                  [else (fn-for-chirper (first todo)
                                        (rest todo)
                                        visited
                                        rsf)]))
          
          ;; ListOfChirper ListOfCnF -> ListOfCnF
          (define (merge-chirpers loc rsf)
            (foldr merge-chirper rsf loc))
          
          ;; Chirper ListOfCnF -> ListOfCnF
          ;; merge chirper to the list of chirpers-and-followers
          (define (merge-chirper c locne)
            (cond [(empty? locne) (list (make-cnf c 1))]
                  [else
                   (if (string=? (chirper-name c) (chirper-name (cnf-chirper (first locne))))
                       (cons (make-cnf c (add1 (cnf-n (first locne))))
                             (rest locne))
                       (cons (first locne)
                             (merge-chirper c (rest locne))))]))
          
          ;; (ListOf Chirper-and-Followers) -> Chirper
          (define (max-followers locnf)
            (cnf-chirper
             (foldr (lambda (c1 c2)
                      (if (> (cnf-n c1) (cnf-n c2))
                          c1
                          c2)) (first locnf) (rest locnf))))]
    
    (max-followers (fn-for-chirper c0 empty empty empty))))




;
;
; PROBLEM 2:
; 
; In UBC's version of How to Code, there are often more than 800 students taking 
; the course in any given semester, meaning there are often over 40 Teaching Assistants. 
; 
; Designing a schedule for them by hand is hard work - luckily we've learned enough now to write 
; a program to do it for us! 
; 
; Below are some data definitions for a simplified version of a TA schedule. There are some 
; number of slots that must be filled, each represented by a natural number. Each TA is 
; available for some of these slots, and has a maximum number of shifts they can work. 
; 
; Design a search program that consumes a list of TAs and a list of Slots, and produces one
; valid schedule where each Slot is assigned to a TA, and no TA is working more than their 
; maximum shifts. If no such schedules exist, produce false. 
;
; You should supplement the given check-expects and remember to follow the recipe!


;; Slot is Natural
;; interp. each TA slot has a number, is the same length, and none overlap

(define-struct ta (name max avail))
;; TA is (make-ta String Natural (listof Slot))
;; interp. the TA's name, number of slots they can work, and slots they're available for

(define SOBA (make-ta "Soba" 2 (list 1 3)))
(define UDON (make-ta "Udon" 1 (list 3 4)))
(define RAMEN (make-ta "Ramen" 1 (list 2)))

(define NOODLE-TAs (list SOBA UDON RAMEN))

(define ERIKA (make-ta "Erika" 1 (list 1 3 7 9)))
(define RYAN (make-ta "Ryan" 1 (list 1 8 10)))
(define REECE (make-ta "Reece" 1 (list 5 6)))
(define GORDON (make-ta "Gordon" 2 (list 2 3 9)))
(define DAVID (make-ta "David" 2 (list 2 8 9)))
(define KATIE (make-ta "Katie" 1 (list 4 6)))
(define AASHISH (make-ta "Aashish" 2 (list 1 10)))
(define GRANT (make-ta "Grant" 2 (list 1 11)))
(define RAEANNE (make-ta "Raeanne" 2 (list 1 11 12)))
(define ERIN (make-ta "Alex" 1 (list 4)))
(define HTC (list ERIKA RYAN REECE GORDON DAVID KATIE AASHISH GRANT RAEANNE))


(define SHIFTS (list 1 2 3 4 5 6 7 8 9 10 11 12))


(define-struct assignment (ta slot))

;; Assignment is (make-assignment TA Slot)
;; interp. the TA is assigned to work the slot

;; Schedule is (listof Assignment)


;; ============================= FUNCTIONS

;; (listof TA) (listof Slot) -> Schedule or false
;; produce valid schedule given TAs and Slots; false if impossible

(check-expect (schedule-tas empty empty) empty)
(check-expect (schedule-tas empty (list 1 2)) false)
(check-expect (schedule-tas (list SOBA) empty) empty)
(check-expect (schedule-tas (list SOBA) (list 1)) (list (make-assignment SOBA 1)))
(check-expect (schedule-tas (list SOBA) (list 2)) false)
(check-expect (schedule-tas (list SOBA) (list 1 3)) (list (make-assignment SOBA 3)
                                                          (make-assignment SOBA 1)))

(check-expect (schedule-tas NOODLE-TAs (list 1 2 3 4)) 
              (list
               (make-assignment UDON 4)
               (make-assignment SOBA 3)
               (make-assignment RAMEN 2)
               (make-assignment SOBA 1)))
(check-expect (schedule-tas NOODLE-TAs (list 1 2 3 4 5)) false)
(check-expect (schedule-tas HTC SHIFTS) false)


(define (schedule-tas tas slots)
  (cond [(empty? slots) empty]
        [(empty? tas) false]
        [else (local [(define (make-schedules s)
                        (if (full-schedule? s slots)
                            s
                            (make-los (next-schedules s tas slots))))
                      (define (make-los los)
                        (cond [(empty? los) false]
                              [else
                               (local [(define try (make-schedules (first los)))]
                                 (if (not (false? try))
                                     try
                                     (make-los (rest los))))]))]
                (make-schedules empty))]))


;; Schedule ListOfSlot -> Boolean
;; produce true if all slots are represented on the schedule
;; ASSUME: schedule is valid
(check-expect (full-schedule? empty (list 1 2)) false)
(check-expect (full-schedule? (list (make-assignment SOBA 1))
                              (list 1 2))
              false)
(check-expect (full-schedule? (list (make-assignment RAMEN 2))
                              (list 1 2))
              false)
(check-expect (full-schedule? (list (make-assignment SOBA 1)
                                    (make-assignment RAMEN 2))
                              (list 1 2))
              true)
(check-expect (full-schedule? (list (make-assignment SOBA 1)
                                    (make-assignment RAMEN 2))
                              (list 1 2 3))
              false)

(define (full-schedule? s slots)
  (local [(define (in-schedule? slot)
            (local [(define (matches? assignment)
                      (= slot (assignment-slot assignment)))]
              (ormap matches? s)))]
    (andmap in-schedule? slots)))


;; Schedule ListofTA ListofSlot -> ListOfSchedule
;; Produce the next listofschedule by filling the first missing "shift"
(check-expect (next-schedules empty (list SOBA) (list 1))
              (list (list (make-assignment SOBA 1))))
(check-expect (next-schedules empty (list SOBA) (list 2)) empty)
(check-expect (next-schedules empty (list SOBA RAMEN) (list 1))
              (list (list (make-assignment SOBA 1))))
(check-expect (next-schedules (list (make-assignment SOBA 1)) (list SOBA RAMEN) (list 1 2))
              (list (list (make-assignment RAMEN 2) (make-assignment SOBA 1))))
(check-expect (next-schedules empty (list SOBA UDON) (list 3))
              (list (list (make-assignment SOBA 3))
                    (list (make-assignment UDON 3))))

(define (next-schedules s tas slots)
  (check-max-shifts tas (check-availability tas (fill-slot tas s (empty-slot s slots)))))



;; (listof TA) (listof Schedule) -> (listof Schedule)
;; filter LOS by max shifts all TAs can work
(check-expect (check-max-shifts (list UDON) (list (list (make-assignment UDON 4)))) (list (list (make-assignment UDON 4))))
(check-expect (check-max-shifts NOODLE-TAs (list (list (make-assignment UDON 4) (make-assignment UDON 3)))) empty)
(check-expect (check-max-shifts NOODLE-TAs (list (list (make-assignment UDON 4) (make-assignment SOBA 3))))
              (list (list (make-assignment UDON 4) (make-assignment SOBA 3))))
(check-expect (check-max-shifts NOODLE-TAs (list (list (make-assignment SOBA 4))
                                                 (list (make-assignment SOBA 3))))
              (list (list (make-assignment SOBA 4))
                    (list (make-assignment SOBA 3))))
(check-expect (check-max-shifts NOODLE-TAs (list (list (make-assignment UDON 4) (make-assignment SOBA 3))
                                                 (list (make-assignment UDON 4) (make-assignment UDON 3))))
              (list (list (make-assignment UDON 4) (make-assignment SOBA 3))))


(define (check-max-shifts tas los)
  (local [(define (check-sched s)
            (exceed-shifts? tas s))]
    (filter check-sched los)))

;; (listof TA) Schedule -> Boolean
;; produce true if schedule doesn't exceed working hours for all TAs
(check-expect (exceed-shifts? NOODLE-TAs (list (make-assignment UDON 1))) true)
(check-expect (exceed-shifts? NOODLE-TAs (list (make-assignment UDON 1)
                                               (make-assignment UDON 2))) false)
(define (exceed-shifts? tas s)
  (local [(define (ok-ta ta)
            (exceed-shift? ta s))]
    (andmap ok-ta tas)))


;; TA Schedule -> Boolean
;; produce false if schedule exceeds max shifts a TA can work
(check-expect (exceed-shift? UDON (list (make-assignment UDON 1))) true)
(check-expect (exceed-shift? UDON (list (make-assignment UDON 1)
                                        (make-assignment UDON 2))) false)
(check-expect (exceed-shift? SOBA (list (make-assignment SOBA 1)
                                        (make-assignment SOBA 2))) true)

(define (exceed-shift? ta s)
  ;; acc is a result-so-far acc, number of shifts a TA has been assigned so far
  (local [(define (count-shift ta s acc)
            (cond [(empty? s) acc]
                  [else (if (string=? (ta-name ta) (ta-name (assignment-ta (first s))))
                            (count-shift ta (rest s) (add1 acc))
                            (count-shift ta (rest s) acc))]))]
    (<= (count-shift ta s 0) (ta-max ta))))




;; (listof TA) (listof Schedule) -> (listof Schedule)
;; filter listof schedule by using only TAs which are available for their shifts
(check-expect (check-availability NOODLE-TAs (list (list (make-assignment SOBA 1) (make-assignment RAMEN 3)))) empty)
(check-expect (check-availability NOODLE-TAs (list (list (make-assignment SOBA 1) (make-assignment RAMEN 2))))
              (list (list (make-assignment SOBA 1) (make-assignment RAMEN 2))))
(check-expect (check-availability NOODLE-TAs (list (list (make-assignment SOBA 1) (make-assignment RAMEN 2))
                                                   (list (make-assignment SOBA 1) (make-assignment RAMEN 3))))
              (list (list (make-assignment SOBA 1) (make-assignment RAMEN 2))))
(check-expect (check-availability NOODLE-TAs (list (list (make-assignment SOBA 1) (make-assignment RAMEN 2))
                                                   (list (make-assignment SOBA 1) (make-assignment UDON 3))))
              (list (list (make-assignment SOBA 1) (make-assignment RAMEN 2))
                    (list (make-assignment SOBA 1) (make-assignment UDON 3))))


(define (check-availability tas los)
  (local [(define (check-sched s)
            (check-availabilities? tas s))]
    (filter check-sched los)))


;; (listof TA) Schedule -> Boolean
;; produce true if schedule is OK for all TAs
(check-expect (check-availabilities? NOODLE-TAs (list (make-assignment SOBA 1) (make-assignment RAMEN 3))) false)
(check-expect (check-availabilities? NOODLE-TAs  (list (make-assignment SOBA 1) (make-assignment RAMEN 2))) true)
(check-expect (check-availabilities? NOODLE-TAs (list (make-assignment SOBA 1) (make-assignment UDON 3))) true)


(define (check-availabilities? tas s)
  (local [(define (ok-ta ta)
            (available? ta s))]
    (andmap ok-ta tas)))


;; TA Schedule -> Boolean
;; produce true if schedule meets TA's requested shifts
(check-expect (available? UDON (list (make-assignment UDON 3))) true)
(check-expect (available? UDON (list (make-assignment RAMEN 3))) true)
(check-expect (available? UDON (list (make-assignment UDON 2))) false)
(check-expect (available? UDON (list (make-assignment RAMEN 3) (make-assignment UDON 4))) true)

(define (available? ta s)
  (cond [(empty? s) true]
        [else (if (string=? (ta-name (assignment-ta (first s))) (ta-name ta))
                  (if (member (assignment-slot (first s)) (ta-avail ta))
                      (available? ta (rest s))
                      false)
                  (available? ta (rest s)))]))


;; (listof TA) Schedule Slot -> ListOfSchedule
;; produce a new schedule by filling the given slot with all TAs
(check-expect (fill-slot (list SOBA RAMEN) empty 1) (list (list (make-assignment SOBA 1))
                                                          (list (make-assignment RAMEN 1))))
(check-expect (fill-slot (list SOBA) (list (make-assignment SOBA 1)) 2) (list (list (make-assignment SOBA 2)
                                                                                    (make-assignment SOBA 1))))

(define (fill-slot tas s slot)
  (local [(define (add-ta ta)
            (append (list (make-assignment ta slot)) s))]
    (map add-ta tas)))

  
;; Schedule ListOfSlot -> Slot
;; find first slot in listofslot, that isn't already accounted for in the schedule
;; ASSUME: schedule is not full
(check-expect (empty-slot empty (list 1 2)) 1)
(check-expect (empty-slot (list (make-assignment SOBA 1)) (list 1 2 3)) 2)
(check-expect (empty-slot (list (make-assignment SOBA 1)
                                (make-assignment RAMEN 2))
                          (list 2 1 4)) 4)


(define (empty-slot s slots)
  (cond [(empty? slots) (error "The schedule should not be full")]
        [(empty? s) (first slots)]
        [(slot-in-schedule? (first slots) s) (empty-slot s (rest slots))]
        [else (first slots)]))


;; Schedule Slot -> Boolean
;; produce true if slot is already included in the schedule
(check-expect (slot-in-schedule? 4 empty) false)
(check-expect (slot-in-schedule? 1 (list (make-assignment SOBA 1))) true)
(check-expect (slot-in-schedule? 2 (list (make-assignment SOBA 1))) false)
(check-expect (slot-in-schedule? 3 (list (make-assignment SOBA 1) (make-assignment RAMEN 2))) false)
(check-expect (slot-in-schedule? 2 (list (make-assignment SOBA 1) (make-assignment RAMEN 2))) true)


(define (slot-in-schedule? slot s)
  (cond [(empty? s) false]
        [(= slot (assignment-slot (first s))) true]
        [else (slot-in-schedule? slot (rest s))]))




