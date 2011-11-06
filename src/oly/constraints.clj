(ns oly.constraints
  (:import [java.util PriorityQueue]))

;; number is final value
;; string is a final value
;; symbol is final value
;; set is individual elements
;; vector [a b] is (range a (inc b))
;; list ([a b] [c d]) is an ordered, disjoint set of a-b ranges (as in vector)

;; dom is map of variable (as keyword) to above domain type
;; propset is a map of propagators and a propagator index

(defn make-CSP 
  "Simple CSP constructor"
  [domains propagators]
  {:dom domains :propset propagators})

(defn add-if-not-present!
  "Add an element to q! if not already present"
  [q! e]
  (when-not (.contains q! e)
    (.add q! e)))

(defn schedule!
  "Schedule propagators into q! that are waiting on the given variables"
  [propset q! vs]
  (doseq [v vs
          p (get-in propset [:index v])]
    (add-if-not-present! q! p))
  q!)

(defn enqueue!
  "Add a seq of propagators into the provided priority queue"
  [q! c]
  (doseq [p (get-in c [:propset :props])]
    (add-if-not-present! q! p))
  q!)

(defn make-queue
  "Make a PriorityQueue with space for an initial n propagators"
  [n]
  (PriorityQueue. (inc n) (comparator #(< (:priority %1)
                                          (:priority %2)))))

(def empty-prop-set
  {:props #{} :index {}})

(defn make-prop-set
  ([] (make-prop-set #{} {}))
  ([props index] {:props props :index index}))

(defn remove-prop
  "Removes a propagator from a propset, including its index entry."
  [{:keys [props index]} p]
  (make-prop-set (disj props p)
                 (let [affected (map first (:interests p))]
                   (reduce #(assoc %1 %2 (disj (%2 %1) p)) index affected))))

(defn propagate
  "Propagate changes until we reach a fixed point"
  ([c]
    (propagate c (enqueue!
                   (make-queue (count (get-in c [:propset :props])))
                   c)))
  ([{:keys [dom propset] :as c} q!]
    (let [p (.poll q!)]
      (if (nil? p)
        c
        (let [[new-dom result events] ((:f p) dom)
              vs (map first events)]
          (cond
            (empty? new-dom) (make-CSP nil nil)
            
            (= :subsumed result)
            (let [new-propset (remove-prop propset p)]
              (recur (make-CSP new-dom new-propset)
                     (schedule! new-propset q! vs)))
        
            (= :fix result) (recur (make-CSP new-dom propset) q!)))))))
    
    

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

(defn add-all-props
  ([ps]
    (add-all-props (make-prop-set) ps))
  ([propset ps]
    (reduce add-propagator propset (flatten ps))))                          

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
  [{:keys [dom propset]}]
  (or (empty? (:props propset))
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
  [{:keys [dom propset]}]
  (println (str "split: " dom))
  (let [[v vs] (first (filter #(not (ground? (val %))) dom))
        chosen (choose-val vs)]
    (list (make-CSP (assoc dom v chosen) propset)
          (make-CSP (assoc dom v (remove-val vs chosen)) propset))))

(defn solve
  "Solve a constraint satisfaction (finite domain) problem. Returns a seq of
valid domain assignments."
  [{:keys [dom propset] :as c}]
  (let [{new-dom :dom :as new-c} (propagate c)]
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

(defn fixed-result [dom]
  "Propagation result where propagator is at a fixed point"
  [dom :fix []])

(defn subsumed-result [dom]
  "Propagation result when a propagator has already been subsumed"
  [dom :subsumed []])

(defn fail-result []
  "Propagation function that results in failure."
  [nil :subsumed []])

(defmulti reduce-single class)
(defmethod reduce-single :default [vs] vs)
(defmethod reduce-single clojure.lang.PersistentHashSet
  [vs]
  (if (= 1 (count vs))
    (first vs)
    vs))

(defn reduction-prop
  "Creates a propagator for a variable that notices when only
   one element is present in the value set and assigns the
   variable."
  [v]
  (create-prop
    (fn [dom]
      (let [dv (dom v)]
        (if (ground? dv)
          (subsumed-result dom)
          (let [rv (reduce-single dv)]
            (if (ground? rv)
              [(assoc dom v rv) :subsumed [[v :assigned]]]
              (fixed-result dom))))))
    0
    [[v :modified]]))


; Used by multimethods to choose propagator implementations
(defn var-type
  "Returns :ground for ground types, :var for domain variables"
  [a]
  (if (ground? a) :ground :var))

;;; Base constraint, equality
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
            (subsumed-result dom)
            (fail-result))
          
          (ground? da)
          (if (member? db da)
            [(assoc dom b da) :subsumed [[b :assigned]]]
            (fail-result))
          
          (ground? db)
          (if (member? da db)
            [(assoc dom a db) :subsumed [[a :assigned]]]
            (fail-result))
          
          :else
          (let [inter (clojure.set/intersection da db)
                cinter (count inter)
                ca (count da)
                cb (count db)]
            (cond
              (= cinter 0)
              (fail-result)
              
              (= cinter 1)
              [(into dom [[a (first inter)] [b (first inter)]])
               :subsumed
               [[a :assigned] [b :assigned]]]
              
              (and (= cinter ca) (= cinter cb))
              (fixed-result dom)
              
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
      (let [dv (dom v)]
        (if (or (and (ground? dv) (= dv g))
                (member? dv g))
            [(assoc dom v g) :subsumed [[v :assigned]]]
            (fail-result))))
    1
    [[v :modified]]))

(defmethod === [:ground :var]
  [g v]
  (=== v g))


;;; Base negation type
(defmulti not=== (fn [a b] [(var-type a) (var-type b)]))

(defmethod not=== [:var :var]
  [a b]
  (create-prop
    (fn [dom]
      (let [da (dom a)
            db (dom b)]
        (cond
          (and (ground? da) (ground? db))
          (if (= da db)
            (fail-result)
            (subsumed-result dom))
          
          (ground? da)
          (if (member? db da)
            [(assoc dom b (remove-val db da)) :subsumed [[b :modified]]]
            (subsumed-result dom))
          
          (ground? db)
          (if (member? da db)
            [(assoc dom a (remove-val da db)) :subsumed [[a :modified]]]
            (subsumed-result dom))

          :else
          (if (empty? (clojure.set/intersection da db))
            (subsumed-result dom)
            (fixed-result dom)))))
    1
    [[a :modified] [b :modified]]))

(defmethod not=== [:var :ground]
  [v g]
  (create-prop
    (fn [dom]
      (let [dv (dom v)]
        (cond
          (and (ground? dv) (= dv g)) (fail-result)
          (ground? dv) (subsumed-result dom)
          (member? dv g) [(assoc dom v (remove-val dv g)) :subsumed [[v :modified]]]
          :else (fixed-result dom))))
    1
    [[v :modified]]))

(defmethod not=== [:ground :var]
  [g v]
  (not=== v g))

;;; All-different
;;; Initially will use braindead approach of adding (not=== a b)
;;; propagators for all a and b in the given list

(defn unordered-pairs
  [es]
  (when (seq es)
    (let [[x & xs] es]
      (concat (map (partial vector x) xs)
              (pairs xs)))))

(defn all-different
  "Braindead all-different implementation, adds (not=== a b)
   propagators for all pairs in the list"
  [xs]
  (map #(apply not=== %) (unordered-pairs xs)))

;;;;;;;;

(defn add-default-props
  "Add in default propagators to reduce singleton values to an assigned value."
  [{:keys [dom propset]}]
  (make-CSP dom (add-all-props propset
                               (map reduction-prop (keys dom)))))

;;;;;;;;

(def p1 (=== :x :y))
(def pp (:f p1))


;;;;;;;;


(defn solve-csp
  [d ps]
  (solve (add-default-props (make-CSP d (add-all-props ps)))))


(def order #{1 2 3 4})
(def arch-domain (zipmap [:espadrilles :flats :pumps :sandals
                          :foot-farm :heels-handcart :shoe-palace :tootsies]
		(repeat order)))
(def arch-prop
  [(all-different [:espadrilles :flats :pumps :sandals])
   (all-different [:foot-farm :heels-handcart :shoe-palace :tootsies])
   (=== :flats :heels-handcart)
   #_(not=== (+ 1 :pumps) :tootsies)
   (=== :foot-farm 2)
   #_(=== (+ 2 :shoe-palace) :sandals)])

(def d1 {:x #{1 2} :y #{2 3}})
(def d2 {:x 4 :y #{5 3}})
(def d3 {:x #{1 2 3} :y #{1 2 3}})

(defn prob1 []
  (solve-csp d1 [(=== :x :y)]))

(defn prob2 []
  (solve-csp d3 [(=== :x :y)]))

(defn prob3 []
  (solve-csp d3 [(not=== :x :y) (not=== 2 :y)]))

(defn prob4 []
  (solve-csp {:x #{1 2}} []))

(defn prob5 []
  (solve (make-CSP {:x #{1 2}} empty-prop-set)))

(defn prob6 []
  (solve-csp {:x #{1 2 3} :y #{1 2 3} :z #{1 2 3}}
             [(not=== :x :y)
              (not=== :y :z)
              (not=== :x :z)]))

(defn prob7 []
  (solve-csp {:x #{1 2 3} :y #{1 2 3} :z #{1 2 3}}
             [(all-different [:x :y :z])]))

(defn prob8 []
  (solve-csp {:x #{1 2} :y #{2 3} :z #{3 4} :a #{4 5} :b #{5 6} :c #{6 7}}
             [(all-different [:x :y :z :a :b :c])]))

(defn prob9 []
  (solve-csp {:x #{1 2} :y #{2 3} :z #{3 4} :a #{4 5} :b #{5 6} :c #{6 7}}
             [(all-different [:x :y :z :a :b :c])
              (not=== :c 7)]))


