(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-option :produce-proofs true) 
(set-option :PULL_NESTED_QUANTIFIERS true)


;*******************************************************************************
;Data types
;*******************************************************************************
;Time
(define-sort Time () Real)

;Most basic sort is Entity
(declare-sort Entity 0)

;Modes
(declare-datatypes () ((Mode maintainSpeed braking accelerating)))

;Location relative to the crossing
(declare-datatypes () ((Location farAway close inInter passed)))

(declare-datatypes () ((Lane XP XM YP YM)))

;Messages
(declare-datatypes () ((MsgType Req Ack)))

(define-sort Message () Int)

;System state
(declare-datatypes () ((SystemState 
			(mk-systemstate (time Time) 
					(mode Mode) 
					(loc Location)
					(x Real)
					(y Real)
					(speed Real)
					(targetSpeed Real)
					(delay Bool)
					(willPass Bool)
					))))


;*******************************************************************************
;Constants
;*******************************************************************************

;Create my Entity
(declare-fun myEntity () Entity)

(define-fun interSize () Real 10.0)

(define-fun closeDist () Real 70.0)

(define-fun acceleration () Real 7.0)

(define-fun speedSlowDownFactor () Real 3.0)

(define-fun laneDist () Real 2.0)

(declare-const states (Array Int SystemState))

;*******************************************************************************
;Mappings
;*******************************************************************************

;Each entity has a priority
(declare-fun prio (Entity) Int)

;Entities can have x and y positions at a given time
(declare-fun x (Entity Time) Real)
(declare-fun y (Entity Time) Real)

(declare-fun InArea (Entity) Bool)

(declare-fun laneOf (Entity) Lane)

;Message related
(declare-fun source (Message) Entity)

(declare-fun sendtime (Message) Time)

(declare-fun type (Message) MsgType)

(declare-fun startt (Message) Time)

(declare-fun endt (Message) Time)

(declare-fun ackOf (Message) Message)

(declare-fun sent (Message) Bool)

(declare-fun received (Message Entity) Bool)

(declare-fun receiveTime (Message Entity) Time)

(declare-fun currentRequest (Entity Time) Message)

(declare-fun valid (Message) Bool)

(declare-fun validationTime (Message) Time)

;*******************************************************************************
;Helper functions
;*******************************************************************************
;Note that some of these functions are actually to be considered
;as a predicate plus an all-quantified constraint on them
;however, for efficiency of the solver it is better to
;define them as functions rather than constraints

(define-fun abs ((a Real)) Real (ite (< a 0.0) (- a) a))

(define-fun min ((a Real) (b Real)) Real (ite (<= a b) a b))
(define-fun max ((a Real) (b Real)) Real (ite (>= a b) a b))

(define-fun conflicts ((m Message) (mp Message)) Bool
  (and (= (type m) Req)
       (= (type mp) Req)
       (< (startt m) (+ (endt mp) 5.0))
       (< (startt mp) (+ (endt m) 5.0))
))
	  
(define-fun inLane ((e Entity)) Bool
  (forall ((t Time))
	  (or (and (= (laneOf e) YP)
		   (= (x e t) laneDist))
	      (and (= (laneOf e) YM)
		   (= (x e t) (- laneDist)))
	      (and (= (laneOf e) XP)
		   (= (y e t) (- laneDist)))
	      (and (= (laneOf e) XM)
		   (= (y e t) laneDist)))))

(define-fun inLaneDir ((e Entity) (t Time) (tp Time)) Bool
  (or (and (= (laneOf e) YP)
	   (>= (y e t) (y e tp)))
      (and (= (laneOf e) YM)
	   (<= (y e t) (y e tp)))
      (and (= (laneOf e) XP)
	   (>= (x e t) (x e tp)))
      (and (= (laneOf e) XM)
	   (<= (x e t) (x e tp)))))

(define-fun EnteredIntersection ((e Entity) (t Time)) Bool 
 (or (and (= (laneOf e) YP)
	  (>= (y e t) (- interSize)))
     (and (= (laneOf e) YM)
	  (<= (y e t) interSize))
     (and (= (laneOf e) XP)
	  (>= (x e t) (- interSize)))
     (and (= (laneOf e) XM)
	  (<= (x e t) interSize))
))

(define-fun LeftIntersection ((e Entity) (t Time)) Bool 
 (or (and (= (laneOf e) YP)
	  (>= (y e t) interSize))
     (and (= (laneOf e) YM)
	  (<= (y e t) (- interSize)))
     (and (= (laneOf e) XP)
	  (>= (x e t) interSize))
     (and (= (laneOf e) XM)
	  (<= (x e t) (- interSize)))
))

(define-fun InIntersection ((e Entity) (t Time)) Bool
  (and (EnteredIntersection e t)
       (not (LeftIntersection e t))))
  
(define-fun hasBeenSent ((m Message) (t Time)) Bool
  (and (sent m)
       (>= t (sendtime m))))

(define-fun hasReceived ((m Message) (e Entity) (t Time)) Bool
  (and (received m e)
       (>= t (receiveTime m e))))



(define-fun hasRequest ((e Entity) (t Time)) Bool
  (and (sent (currentRequest e t))
       (= (source (currentRequest e t)) e)
       (<= (sendtime (currentRequest e t)) t)
       (= (type (currentRequest e t)) Req)
       (> (endt (currentRequest e t)) t)))

(define-fun accepted ((m Message) (e Entity)) Bool
  (and (received m e)
       (or (not (hasRequest e (receiveTime m e)))
	   (not (conflicts m (currentRequest e (receiveTime m e))))
	   (< (prio e) (prio (source m))))))
	 

(define-fun hasResource ((e Entity) (t Time)) Bool
   (and 
    (hasRequest e t)
    (valid (currentRequest e t))
    (<= (validationTime (currentRequest e t)) t)
    (<= (startt (currentRequest e t)) t)
    (>= (endt (currentRequest e t)) t)
    ))

(define-fun getState ((idx Int)) SystemState
  (select states idx))

(define-fun getSucc ((s SystemState)) SystemState 
  (ite (delay s)
       ;Continuous case
       (let ((newTime (+ (time s)
			 (min (ite (= (loc s) farAway)
				   (/ (- (- closeDist) (x s)) 1000.0)
				   (ite (= (loc s) close)
					(/ (- (- interSize) (x s)) 1000.0)
					(ite (= (loc s) inInter)
					     (/ (- interSize (x s)) 1000.0)
					     0.001)))
			      0.001)))
	     (newSpeed (targetSpeed s)))
	 (mk-systemstate newTime
			 (mode s)
			 (loc s)
			 (+ (x s) (* (/ (+ (speed s) newSpeed) 2.0) (- newTime (time s))))
			 (y s)
			 newSpeed
			 (targetSpeed s)
			 (not (delay s))
			 (willPass s)
		       ))
       ;Discrete case
       (let ((newloc (ite (= (x s) (- closeDist))
			  close
			  (ite (= (x s) (- interSize))
			       inInter
			       (ite (= (x s) interSize)
				    passed
				    (loc s)))))
	     (newWillPass (ite (= (x s) (- closeDist))
			       (and (hasResource myEntity (time s))
				    (>= (endt (currentRequest myEntity (time s))) (+ (time s) 100.0)))
			       (willPass s))))
	 (mk-systemstate (time s)
			 (mode s)
			 newloc
			 (x s)
			 (y s)
			 (speed s)
			 (ite (= newloc close)
			      (ite newWillPass
				   2.0
				   0.0)
			      2.0)
			 (not (delay s))
			 newWillPass
			 ))))

;*******************************************************************************
;State machine
;*******************************************************************************

(define-fun validLocations ((s SystemState)) Bool
  (and (=> (= (loc s) farAway) (<= (x s) (- closeDist)))
       (=> (= (loc s) close) (and (>= (x s) (- closeDist)) (<= (x s) (- interSize))))
       (=> (= (loc s) inInter) (and (>= (x s) (- interSize)) (<= (x s) interSize)))
       (=> (= (loc s) passed) (>= (x s) interSize))))


(define-fun Compatible ((s SystemState)) Bool 
  (and 
       (or 
       	(= (speed s) 0.5)
       	(= (speed s) 1.0)
       	(= (speed s) 1.5)
       	(= (speed s) 2.0)
       	(= (speed s) 2.5)
       	(= (speed s) 3.0)
       	(= (speed s) 3.5)
       	(= (speed s) 4.0)
       	(= (speed s) 4.5)
       	(= (speed s) 5.0)
       	(= (speed s) 5.5)
       	(= (speed s) 6.0)
       	(= (speed s) 6.5)
       	(= (speed s) 7.0)
       	(= (speed s) 7.5)
       	(= (speed s) 8.0)
       	(= (speed s) 8.5)
       	(= (speed s) 9.0)
       	(= (speed s) 9.5)
       	(= (speed s) 10.0)
       	(= (speed s) 10.5)
       	(= (speed s) 11.0)
       	(= (speed s) 11.5)
       	(= (speed s) 12.0)
       	(= (speed s) 12.5)
       	(= (speed s) 13.0)
       	(= (speed s) 13.5)
       	(= (speed s) 14.0)
       	(= (speed s) 14.5)
       	(= (speed s) 15.0)
       	(= (speed s) 15.5)
       	(= (speed s) 16.0)
       	(= (speed s) 16.5)
       	(= (speed s) 17.0)
       	(= (speed s) 17.5)
       	(= (speed s) 18.0)
       	(= (speed s) 18.5)
       	(= (speed s) 19.0)
       	(= (speed s) 19.5)
       	(= (speed s) 20.0)
       	(= (speed s) 0.0))
       (validLocations s)
       (= (y s) (- laneDist))
       ))

(define-fun allowedMovement ((s SystemState) (sp SystemState)) Bool 
  (= (x sp) (+ (x s) (* (/ (+ (speed s) (speed sp)) 2.0) (- (time sp) (time s))))))

(define-fun allowedSpeedChange ((s SystemState) (sp SystemState)) Bool 
  (ite (= (targetSpeed s) (speed s))
       (= (speed sp) (speed s))
       (ite (= (- (time sp) (time s)) 
	       (/ (abs (- (targetSpeed s) (speed s))) acceleration))
	    (= (speed sp) (targetSpeed s))
	    (let ((t (- (time sp) (time s))))
	      (ite (< (targetSpeed s) (speed s))
		   (and (<= (speed sp) (- (speed s) (* t acceleration))) 
			(>= (speed sp) (targetSpeed s)))
		   (and (>= (speed sp) (+ (speed s) (* t acceleration)))
			(<= (speed sp) (targetSpeed s))))))))

(define-fun continuousConsts ((s SystemState) (sp SystemState)) Bool 
  (and (= (mode s) (mode sp)) 
       (= (targetSpeed s) (targetSpeed sp))
       (= (loc s) (loc sp))
       (= (willPass s) (willPass sp))
       ))

(define-fun timePass  ((s SystemState) (sp SystemState)) Bool 
  (> (time sp) (time s)))

(define-fun speedChangeDuration ((s SystemState) (sp SystemState)) Bool
  (=> (not (= (targetSpeed s) (speed s)))
      (<= (time sp) (+ (time s)
		       (/ (abs (- (targetSpeed s) (speed s))) acceleration)))))

(define-fun ContinuousTrans ((s SystemState) (sp SystemState)) Bool 
  (and  (timePass s sp)
	(continuousConsts s sp)
	(speedChangeDuration s sp)
	(allowedSpeedChange s sp)
	(allowedMovement s sp)
	(Compatible sp)
	))

(define-fun discreteConsts ((s SystemState) (sp SystemState)) Bool 
  (and (= (time s) (time sp)) 
       (= (speed s) (speed sp))
       (= (x s) (x sp))
       (= (y s) (y sp))))
  
(define-fun willPassDecision ((s SystemState) (sp SystemState)) Bool 
  (ite (= (x s) (- closeDist))
       (ite (and (hasResource myEntity (time s))
		 (>= (endt (currentRequest myEntity (time s))) (+ (time s) 100.0)))
	    (willPass sp)
	    (not (willPass sp)))
       (ite (and (= (loc sp) close)
		 (not (willPass s))
		 (hasResource myEntity (time s))
		 (>= (endt (currentRequest myEntity (time s))) (+ (time s) 100.0))
		 (>= (targetSpeed sp) 2.0))
	    (willPass sp)
	    (= (willPass s) (willPass sp)))))

(define-fun changeLocationState ((s SystemState) (sp SystemState)) Bool 
  (ite (and (>= (x s) (- closeDist)) (< (x s) (- interSize)))
       (= (loc sp) close)
       (ite (and (>= (x s) (- interSize)) (< (x s) interSize))
	    (= (loc sp) inInter)
	    (ite (>= (x s) interSize)
		 (= (loc sp) passed)
		 (= (loc sp) farAway)))))

(define-fun changeTargetSpeed ((s SystemState) (sp SystemState)) Bool 
  (ite (= (loc sp) close)
       (ite (willPass sp)
	    (= (targetSpeed sp) 2.0)
	    (= (targetSpeed sp) 0.0))
       (ite (= (loc sp) inInter)
	    (= (targetSpeed sp) 2.0)
	    (or (= (targetSpeed sp) 0.0)
		(= (targetSpeed sp) 2.0)
		(= (targetSpeed sp) 10.0))
;	    (and (>= (targetSpeed sp) 0.0)
;		 (<= (targetSpeed sp) 14.0)
		 )))
  
(define-fun DiscreteTrans ((s SystemState) (sp SystemState)) Bool 
  (and (discreteConsts s sp)
       (Compatible sp)
       (willPassDecision s sp)
       (changeLocationState s sp)
       (changeTargetSpeed s sp)
       ))

(define-fun T ((s SystemState) (sp SystemState)) Bool 
  (or (and (ContinuousTrans s sp) 
	   (delay s) 
	   (not (delay sp)))
      (and (DiscreteTrans s sp) 
	   (not (delay s)) 
	   (delay sp))
  ))

(define-fun Ts ((idx1 Int) (idx2 Int)) Bool
  (T (getState idx1) (getState idx2)))

;*******************************************************************************
;Safety properties
;*******************************************************************************

(define-fun stateDistSafe ((s SystemState)) Bool
  (forall ((e Entity)) (or (= e myEntity)
			   (not (InArea e))
			   (< 5.0 (abs (- (x s) (x e (time s)))))
			   (< 3.0 (abs (- (y s) (y e (time s))))))))

(define-fun inInterHasResSafe ((s SystemState)) Bool
  (=> (and (< (x s) interSize) (>= (x s) (- interSize)))
      (and (hasResource myEntity (time s))
	   (willPass s)
	   (>= (endt (currentRequest myEntity (time s))) (+ (time s) (- interSize (x s))))
	   (= (targetSpeed s) 2.0))
      ))

(define-fun beforeInterSpeed ((s SystemState)) Bool
  (=> (= (loc s) close)
      (ite (willPass s)
	   (and (hasResource myEntity (time s))
		(>= (endt (currentRequest myEntity (time s))) (+ (time s) (- 15.0 (x s))))
		(= (targetSpeed s) 2.0))
	   (<= (speed s) (/ (- (- interSize) (x s)) speedSlowDownFactor)))))

;Safety function
(define-fun Safe ((s SystemState)) Bool 
  (and (stateDistSafe s)
       (inInterHasResSafe s)
       (beforeInterSpeed s)
       (Compatible s)
       ))

(define-fun Safes ((idx Int)) Bool
  (Safe (getState idx)))

;*******************************************************************************
;Assertions
;*******************************************************************************

;myEntity is in the area
;-------------------------------------------------------------------------------
(assert (! (InArea myEntity) :named myEntityInArea))
(echo "myEntityInArea")
(check-sat)


;It takes non-zero time for a message to be delivered
;-------------------------------------------------------------------------------
(assert (! (forall ((m Message) (e Entity)) 
		   (> (receiveTime m e) (sendtime m)))
	   :name flighttime))


;If a message is reveived at time t, then it has been sent at an
;earlier (or the same) time
;-------------------------------------------------------------------------------
(assert (! (forall ((m Message) (e Entity) (t Time)) 
		   (=> (received m e)
		       (sent m))) :named recMsgWasSent))
(echo "recMsgWasSent")
(check-sat)

;; ;Oll other cars must have x = 0 at all times
;; ;-------------------------------------------------------------------------------
;; (assert (! (forall ((e Entity)) 
;; 		   (or 
;; 		    (= (laneOf e) YP) 
;; 		    (= (laneOf e) YM) 
;; 		    (= myEntity e))) :named otherEntityLanes))
;; (echo "otherEntityLanes")
;; (check-sat)

;XP dist
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity) (s SystemState)) 
		   (or (= myEntity e)
		       (=> (= (laneOf e) XP)
			   (> (abs (- (x s) (x e (time s)))) 5.0))))
	   :named xpdist))
(echo "xpdist")
(check-sat)


;All otherentities will keep in their lane
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity)) (or (= e myEntity)
				    (inLane e))) :named otherEntitiesInLane))
(echo "otherEntitiesInLane")
(check-sat)


;If an entity is in the intersection then it is also in the area
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity) (t Time)) 
		   (=> (InIntersection e t) (InArea e))) :named ininterinarea))
(echo "ininterinarea")
(check-sat)


;If an Ack message has been sent by node e, then it has received a req
;message before
;-------------------------------------------------------------------------------
(assert (! (forall ((m Message)) 
		   (=> (and (sent m)
			    (= (type m) Ack))
		       (and (received (ackOf m) (source m))
			    (= (type (ackOf m)) Req)
			    (<= (receiveTime (ackOf m) (source m)) (sendtime m))
			    (not (= m (ackOf m)))
			    ))) :named ackToReq))
(echo "ackToReq")
(check-sat)

;If a message is valid, then the validation time is smaller than the
;starttime and larger than the sendtime
;-------------------------------------------------------------------------------
(assert (! (forall ((m Message)) 
		   (=> (valid m)
		       (and 
			(< (validationTime m) (startt m))
			(> (validationTime m) (sendtime m))
			(sent m)
			))):named validtime))
(echo "validtime")
(check-sat)


;If a message is validated, then the source node has received Acks
;from all entities in the area
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity) (m Message) (ep Entity))
		  (=> (and (valid m)
			   (= e (source m))
			   (InArea e)
			   (InArea ep)
			   (not (= ep e)))
		      (and 
		       (exists ((mp Message))
				   (and 
				    (= (source mp) ep)
				    (received mp e)
				    (<= (receiveTime mp e) (validationTime m))
				    (= (type mp) Ack)
				    (= (ackOf mp) m)
				    ))
		       )))
	   :named validMsg))
(echo "validMsg")
(check-sat)


;If a message is validated, then the sender has not received a
;conflicting Req from a higher priority entity
;-------------------------------------------------------------------------------
(assert (! (forall ((m Message) (mp Message) (t Time)) 
		   (=> (and (valid m)
			    (hasReceived mp (source m) (validationTime m))
			    (not (= m mp)))
		       (or  (< (prio (source mp)) (prio (source m)))
			    (not (conflicts m mp))
			    (not (= (type mp) Req))))) :named validnoconfl))
(echo "validnoconf")
(check-sat)

;CurrentRequest cannot conflict with a received request
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity) (t Time) (m Message))
		   (=> (and (hasRequest e t)
			    (received m e)
			    (accepted m e)
			    (not (= e (source m))))
		       (not (conflicts m (currentRequest e t)))))
	   :named noConfReq))

;If another car is in the intersection, it must have the resource
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity) (t Time)) (or (= myEntity e) 
					     (=> (EnteredIntersection e t) 
						 (hasResource e t)
						 ))) :named inInterHasRes))
(echo "inInterHasRes")
(check-sat)

;If another car has the resource, it must be in the area
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity) (t Time)) (or (= myEntity e)
					     (=> (hasResource e t)
						 (InArea e)))) :named hasResInArea))
(echo "hasresInArea")
(check-sat)


;Priorities are unique (at least within the active area)
;-------------------------------------------------------------------------------
(assert (! (forall ((e Entity) (ep Entity))
		   (or (not (InArea e)) 
		       (not (InArea ep)) 
		       (= e ep) 
		       (not (= (prio e) (prio ep)))))
		       :named uniquePrios))
(echo "uniquePrios")
(check-sat)

(assert (! (forall ((e Entity) (t Time) (tp Time))
		   (= (currentRequest e t) (currentRequest e tp)))
	   :named currentreqstays))
(echo "currentreqstays")
(check-sat)


;*******************************************************************************
;Model checks
;*******************************************************************************

;-------------------------------------------------------------------------------
(push)
(echo "Check that myEntity can have the resource")
(echo "Expect: sat")
(assert (exists ((t Time)) (hasResource myEntity t)))
(check-sat)
(echo "")
(pop)

;-------------------------------------------------------------------------------
(push)
(echo "Check that having a resource means that the current request is valid")
(echo "Expect: unsat")
(assert (not (forall ((e Entity) (t Time))
		     (=> (hasResource e t)
			 (valid (currentRequest e t))))))
(check-sat)
(echo "")
(pop)

;-------------------------------------------------------------------------------
(push)
(echo "Check that two nodes cannot have valid and conflicting requests")
(echo "Expect: unsat")
(assert  (exists ((e Entity) (ep Entity) (t Time))
		 (and (valid (currentRequest e t))
		      (hasRequest e t)
		      (hasRequest ep t)
		      (InArea e)
		      (not (= e ep))
		      (InArea ep)
		      (valid (currentRequest ep t))
		      (conflicts  (currentRequest e t)  (currentRequest ep t)))))
(check-sat)
;(get-model)
(echo "")
(pop)

;-------------------------------------------------------------------------------
(push)
(assert (! (and (= (mode (getState 0)) maintainSpeed)
		(= (targetSpeed (getState 0)) 2.0)
		(= (time (getState 0)) 0.0)
		(= (speed (getState 0)) 1.0)
		(= (x (getState 0)) (- 100.0))
		(= (y (getState 0)) (- laneDist))
		(not (willPass (getState 0)))
		(forall ((c Entity))  (not (hasResource c (time (getState 0)))))
		(Compatible (getState 0))
		(not (exists ((m Message)) 
			     (and (= (source m) myEntity)
				  (hasBeenSent m (time (getState 0))))))
		) :named initass))

;-------------------------------------------------------------------------------
(push)
(echo "Check if only one entity can have the resource (should be unsat)")
(echo "Expect: unsat")
(assert (not (forall ((e Entity) (ep Entity) (t Time))
		     (=> (and (hasResource e t) (not (= e ep)))
			 (not (hasResource ep t))))))
(check-sat)
;(get-model)
(echo "")
(pop)

;-------------------------------------------------------------------------------
(push)
(echo "Check if init state is satisfiable")
(echo "Expect: sat")
(assert (Safes 0))
(check-sat)
(echo "")
(pop)

;-------------------------------------------------------------------------------
(push)
(echo "Check if initial states are safe")
(echo "Expect: unsat")
(assert (and (Ts 0 1) (Ts 1 2) (Ts 2 3) (Ts 3 4)
	     (or (not (Safes 0)) 
		 (not (Safes 1)) 
		 (not (Safes 2))
		 (not (Safes 3))
		 (not (Safes 4))
		 )))
(check-sat)
;(get-model)
(echo "")
(pop)

;-------------------------------------------------------------------------------
(push)
(echo "Check if there is a path")
(echo "Expect: sat")
(assert (and (Ts 0 1) (Ts 1 2) (Ts 2 3) (Ts 3 4) 
	     (Ts 4 5) (Ts 5 6) (Ts 6 7) (Ts 7 8)
	     (Ts 8 9) (Ts 9 10) (Ts 10 11) (Ts 11 12)
	     (>= (x (getState 12)) closeDist)))
(check-sat)
;(get-unsat-core)
;(get-model)
(echo "")
(pop)

;; ;-------------------------------------------------------------------------------

(pop)

;-------------------------------------------------------------------------------
(push)
(echo "Try to prove safety for system")
(echo "Expect: unsat")
(assert (and (Ts 1 2) (Ts 2 3) 
	;(Ts 3 4) (Ts 4 5) (Ts 5 6) 
	     (Safes 1) 
	     (Safes 2) 
	     ;(Safes 3) (Safes 4) (Safes 5)
	     (not (Safes 2))
	     ))
(check-sat)
;(get-unsat-core)
;(get-model)
(echo "")
(pop)


;-------------------------------------------------------------------------------
(push)
(echo "Prove that discretetrans cannot lead to incompatibility")
(echo "Expect: unsat")
;(declare-const s SystemState)
(assert (and ;(Safes 1)
	 (Compatible (getState 1))
	 (discreteConsts (getState 1) (getState 2))
	 (willPassDecision (getState 1) (getState 2))
	 (changeLocationState (getState 1) (getState 2))
	 (changeTargetSpeed (getState 1) (getState 2))
	 (not (Compatible (getState 2)))
	 ))
(check-sat)
;(get-unsat-core)
;(get-model)
(echo "")
(pop)

(push)
(echo "Prove that discretetrans cannot lead to deadlock")
(echo "Expect: unsat")
(assert (and (Compatible (getState 1))
	     (not (delay (getState 1)))
	     ;; (not (and (Compatible (getSucc (getState 1)))
	     ;; 	       (discreteConsts (getState 1) (getSucc (getState 1)))
	     ;; 	       (changeLocationState (getState 1) (getSucc (getState 1)))
	     ;; 	       (changeTargetSpeed  (getState 1) (getSucc (getState 1)))
	     ;; 	       (willPassDecision (getState 1) (getSucc (getState 1)))
	     (not (DiscreteTrans (getState 1) (getSucc (getState 1))))
	     ))

(check-sat)
;(get-model)
(echo "")
(pop)


(push)
(echo "Prove that continuoustrans cannot lead to deadlock")
(echo "Expect: unsat")
(assert (and (DiscreteTrans (getState 1) (getState 2))
	     (delay (getState 2))
	     (not (ContinuousTrans (getState 2) (getSucc (getState 2))))
	     ;; (not (and (Compatible (getSucc (getState 2)))
	     ;; 	       (continuousConsts (getState 2) (getSucc (getState 2)))
	     ;; 	       (timePass (getState 2) (getSucc (getState 2)))
	     ;; 	       (allowedMovement  (getState 2) (getSucc (getState 2)))
	     ;; 	       (allowedSpeedChange (getState 2) (getSucc (getState 2)))
	     ;; 	       (speedChangeDuration (getState 2) (getSucc (getState 2)))
	     ;; 	       ))
	     ;; 	       (willPassDecision (getState 1) (getSucc (getState 1)))
	     ))

(check-sat)
;(get-model)
(echo "")
(pop)


(push)
(echo "Prove freedom from deadlock")
(echo "Expect: unsat")
(assert (and (Ts 1 2)
	     (not (T (getState 2) (getSucc (getState 2))))))
	     ;; (not (and (Compatible (getSucc (getState 2)))
	     ;; 	       (continuousConsts (getState 2) (getSucc (getState 2)))
	     ;; 	       (timePass (getState 2) (getSucc (getState 2)))
	     ;; 	       (allowedMovement  (getState 2) (getSucc (getState 2)))
	     ;; 	       (allowedSpeedChange (getState 2) (getSucc (getState 2)))
	     ;; 	       (speedChangeDuration (getState 2) (getSucc (getState 2)))
	     ;; 	       ))
	     ;; 	       (willPassDecision (getState 1) (getSucc (getState 1)))

(check-sat)
;(get-model)
(echo "")
(pop)