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

(defn ground?
  "Returns true if the given variable has a final value in the given domain."
  [dom v]
  (let [vval (v dom)]
    (or (number? vval)
        (string? vval)
        (symbol? vval))))

(defn domain-solved?
  "Returns true if all the variables have been assigned a final value,
or if the propagators have been exhausted."
  [{:keys [dom props]}]
  (or (empty? props)
      (every? (partial ground? dom) dom)))

(defn choose-val
  "Pick one item from a domain entry"
  [vs]
  2)

(defn remove-val
  "Remove a value from a domain entry"
  [vs v]
  (dissoc vs 2))

(defn split-constraints
  "Returns a seq of smaller CSPs. This version does a simple split by finding
a variable without a final value and returning two CSPs: one where the
variable is assigned to one of the possible values, and another where that
same value has been removed from the possible values of that same variable."
  [{:keys [dom props]}]
  (let [[v vs] (first (remove #(not (ground? dom %2)) dom))
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
      (domain-solved? new-c) (list new-c)
      :else (mapcat solve (split-constraints new-c)))))

	  


(def order #{1 2 3 4})
(def arch-domain (zipmap [:espadrilles :flats :pumps :sandals
							:foot-farm :heels-handcart :shoe-palace :tootsies]
						(repeat order)))

#_(def arch-prop (prop-add (all-different [:espadrilles :flats :pumps :sandals])
						(all-different [:foot-farm :heels-handcart :shoe-palace :tootsies])))
						
#_(defn prob1 []
  (let [d {:x #{1 2} :y #{2 3}}
        p #{(prop= 4 (prop+ :x :y))}]
    (solve-constraints (make-CSP d p))))


(def d1 {:x #{1 2} :y #{2 3}})
(def d2 {:x 4 :y #{5 3}})

#_(defprotocol Domain
  (empty? [this])
  (count [this]))

