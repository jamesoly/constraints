(ns oly.constraints)

;; number is final value
;; string is a final value
;; symbol is final value
;; set is individual elements
;; vector [a b] is (range a (inc b))
;; list ([a b] [c d]) is an ordered, disjoint set of a-b ranges (as in vector)

;; dom is map of variable (as keyword) to above domain type
;; props is a collection (set? vector?) of propagators

(defn make-CSP 
  "Simple CSP constructor"
  [domains propagators]
  {:dom domains :props propagators})

(defn propagate
  "Null propagation, does not apply propagators."
  [{:keys [dom props] :as c}]
  c)

(def empty-prop-set
  {:props #{} :index {}})
(defn make-prop-set
  ([] (make-prop-set #{} {}))
  ([props index] {:props props :index index}))

(defn add-propagator
  "Add a propagator to the propagator set and index what variables
   it is interested in."
  ([prop]
    (add-propagator (make-prop-set) prop))
  ([{:keys [props index]} {:keys [f priority interests] :as prop}]
    (make-prop-set
      (conj props prop)
      (merge-with clojure.set/union
                  index
                  (into {} (for [[v ev] interests] [v #{prop}]))))))    

; Is the type a ground (fully-assigned) type?
(defmulti ground? class)
(defmethod ground? :default [_] false)
(defmethod ground? java.lang.Long [_] true)
(defmethod ground? java.lang.String [_] true)
(defmethod ground? clojure.lang.Symbol [_] true)

; Does this domain include i as a member?
(defmulti member? (fn [d i] (class d)))
(defmethod member? clojure.lang.PersistentHashSet [d i] (d i))

(defn domain-solved?
  "Returns true if all the variables have been assigned a final value,
or if the propagators have been exhausted."
  [{:keys [dom props]}]
  (or (empty? props)
      (every? #(ground? (val %)) dom)))

; Choose an arbitrary member from a domain type. Used to split CSPs
(defmulti choose-val class)
(defmethod choose-val clojure.lang.PersistentHashSet
  [a]
  (first a))

; Remove a member from a domain type
(defmulti remove-val (fn [d _] (class d)))
(defmethod remove-val clojure.lang.PersistentHashSet
  [d i]
  (disj d i))

(defn split-constraints
  "Returns a seq of smaller CSPs. This version does a simple split by finding
a variable without a final value and returning two CSPs: one where the
variable is assigned to one of the possible values, and another where that
same value has been removed from the possible values of that same variable."
  [{:keys [dom props]}]
  (println (str "split: " dom))
  (let [[v vs] (first (filter #(not (ground? (val %))) dom))
        chosen (choose-val vs)]
    (list (make-CSP (assoc dom v chosen) props)
          (make-CSP (assoc dom v (remove-val vs chosen)) props))))

(defn solve
  "Solve a constraint satisfaction (finite domain) problem. Returns a seq of
valid domain assignments."
  [{:keys [dom props] :as c}]
  (let [{new-dom :dom new-props :props :as new-c} (propagate c)]
    (cond
      (nil? new-dom) nil
      (domain-solved? new-c) (list new-dom)
      :else (mapcat solve (split-constraints new-c)))))

; A propagator is a map with a propagator function, a priority, and
; a list of events the propagator is interested in.
;
; A propagator function is a function from a full domain to a
; vector [new-dom result [events]]. Result can be :subsumed (propagator
; can never prune a domain anymore) or :fix (propagator is at a fixed
; point) [and later could be :no-fix if multi-staged propagators are
; implemented].
;
; Events are a pair of a variable and an event indicator, such as
; :assigned (variable has been fully assigned), :domain-change
; (unspecified change), :lower-bound, :upper-bound, :both-bounds. They
; are used to schedule interested propagators. Note: currently these
; events are just the variables, not the event indicator.

(defn create-prop [f pri interest]
  "Creates a propagator given a propagation function, priority, and
   a vector of variables whose changes will trigger the propagator
   to be rescheduled. This vector will eventually incorporate what
   type of modification events will cause a reschedule."
  {:f f :priority pri :interests interest})

(defn empty-prop-result [dom]
  "Propagation function that can make no changes to the domains."
  [dom :subsumed []])
(def empty-propagator (create-prop empty-prop-result 1 []))

(defn null-prop-result [dom]
  "Propagation function that results in failure."
  [nil :subsumed []])
(def null-propagator (create-prop null-prop-result 1 []))

; Used by multimethods to choose propagator implementations
(defn var-type
  "Returns :ground for ground types, :var for domain variables"
  [a]
  (if (ground? a) :ground :var))

; Base constraint, equality
(defmulti === (fn [a b] [(var-type a) (var-type b)]))

(defmethod === [:var :var]
  [a b]
  (create-prop
    (fn [dom]
      (let [da (dom a)
            db (dom b)]
        (cond
          (and (ground? da) (ground? db))
          (if (= da db)
            (empty-prop-result dom)
            (null-prop-result dom))
          
          (ground? da)
          (if (member? db da)
            [(assoc dom b da) :subsumed [[b :assigned]]]
            (null-prop-result dom))
          
          (ground? db)
          (if (member? da db)
            [(assoc dom a db) :subsumed [[a :assigned]]]
            (null-prop-result dom))
          
          :else
          (let [inter (clojure.set/intersection da db)
                cinter (count inter)
                ca (count da)
                cb (count db)]
            (cond
              (= cinter 0)
              (null-prop-result dom)
              
              (= cinter 1)
              [(into dom [[a (first inter)] [b (first inter)]])
               :subsumed
               [[a :assigned] [b :assigned]]]
              
              (and (= cinter ca) (= cinter cb))
              (empty-prop-result dom)
              
              (= cinter ca)
              [(assoc dom b inter) :fix [b :modified]]
              
              (= cinter cb)
              [(assoc dom a inter) :fix [a :modified]]
              
              :else
              [(into dom [[a inter] [b inter]])
               :fix
               [[a :modified] [b :modified]]])))))
    1
    [[a :modified] [b :modified]]))

(defmethod === [:var :ground]
  [v g]
  (create-prop
    (fn [dom]
      (if ((dom v) g)
        [(assoc dom v g) :subsumed [[v :assigned]]]
        (null-prop-result dom)))
    1
    [[v :modified]]))

(defmethod === [:ground :var]
  [g v]
  (=== v g))


;;;;;;;;

(def p1 (=== :x :y))
(def pp (:f p1))


;;;;;;;;

(def order #{1 2 3 4})
(def arch-domain (zipmap [:espadrilles :flats :pumps :sandals
                          :foot-farm :heels-handcart :shoe-palace :tootsies]
		(repeat order)))
#_(def arch-prop
    (prop-add
      (all-different [:espadrilles :flats :pumps :sandals])
      (all-different [:foot-farm :heels-handcart :shoe-palace :tootsies])
      (=== :flats :heels-handcart)
      (not=== (+ 1 :pumps) :tootsies)
      (=== :foot-farm 2)
      (=== (+ 2 :shoe-palace) :sandals)))



#_(defn prob1 []
  (let [d {:x #{1 2} :y #{2 3}}
        p #{(prop= 4 (prop+ :x :y))}]
    (solve-constraints (make-CSP d p))))


(def d1 {:x #{1 2} :y #{2 3}})
(def d2 {:x 4 :y #{5 3}})

(defn prob2 []
  (let [d {:x #{1 2 3} :y #{1 2 3}}
        p #{(=== :x 1)}]
    (solve (make-CSP d p))))


